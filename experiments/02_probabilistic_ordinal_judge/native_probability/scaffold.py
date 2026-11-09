"""TLDR: Offline, hash-bound six-category forecast preparation and evaluation; no inference or fitting."""
import argparse
from collections import Counter
from decimal import Decimal
import hashlib
import json
import math
from pathlib import Path

VERSION = "native_probability_offline_v1"
METRICS_VERSION = "native_probability_metrics_v2"
FILE_ROLES = {"python_source", "candidate_lean", "gold_reference_lean", "rubric"}
VISIBILITY = "complete_candidate_and_reference_artifacts_including_proof_bodies"
MAX_ARTIFACTS = 10000
MAX_RATINGS = 100000
MAX_FILE_BYTES = 16 * 1024 * 1024
MAX_JSON_BYTES = 32 * 1024 * 1024
MAX_RESPONSE_BYTES = 65536


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key")
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError("Nonfinite JSON constant")


def load_json(text, decimal=False):
    require(isinstance(text, str), "JSON input must be text")
    require(len(text.encode()) <= MAX_JSON_BYTES, "JSON input too large")
    return json.loads(text, object_pairs_hook=unique_object,
                      parse_constant=reject_constant,
                      parse_float=Decimal if decimal else float)


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False, allow_nan=False).encode()


def digest(value):
    return hashlib.sha256(encoded(value)).hexdigest()


def exact_keys(value, keys, label):
    require(isinstance(value, dict) and set(value) == set(keys), label + " keys differ")


def nonempty_string(value, label):
    require(isinstance(value, str) and bool(value.strip()), label + " must be nonempty text")


def file_record(root, relative):
    nonempty_string(relative, "File path")
    require(not Path(relative).is_absolute(), "File paths must be relative")
    path = (Path(root).resolve() / relative).resolve()
    require(path.is_relative_to(Path(root).resolve()), "File path escapes input root")
    require(path.is_file() and path.stat().st_size <= MAX_FILE_BYTES, "Missing/oversized input file")
    data = path.read_bytes()
    require(len(data) <= MAX_FILE_BYTES, "Input grew beyond file limit")
    return {"path": relative, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def freeze_manifest(spec, root):
    """Hash exact local files; metadata declares a condition, not a verified model execution."""
    exact_keys(spec, {"condition_id", "split", "proof_visibility", "judge_configuration", "artifacts"}, "Spec")
    nonempty_string(spec["condition_id"], "Condition ID")
    require(spec["split"] in {"train", "validation", "test"}, "Unknown split")
    require(spec["proof_visibility"] == VISIBILITY, "Only complete-artifact visibility is supported")
    config = spec["judge_configuration"]
    exact_keys(config, {"judge_id", "model_id", "harness", "effort", "training_method", "prompt_sha256"}, "Judge configuration")
    for key, value in config.items():
        nonempty_string(value, key)
    require(config["training_method"] in {"method_2_correlation", "method_4_proper_loss", "fixed_baseline"}, "Unknown training method")
    require(len(config["prompt_sha256"]) == 64 and all(c in "0123456789abcdef" for c in config["prompt_sha256"]), "Invalid prompt digest")
    require(isinstance(spec["artifacts"], list) and 0 < len(spec["artifacts"]) <= MAX_ARTIFACTS, "Invalid artifact count")
    artifacts, seen = [], set()
    for item in spec["artifacts"]:
        exact_keys(item, {"artifact_id", "task_family_id", "agent_id", "files"}, "Artifact")
        for key in ("artifact_id", "task_family_id", "agent_id"):
            nonempty_string(item[key], key)
        require(item["artifact_id"] not in seen, "Duplicate artifact ID")
        seen.add(item["artifact_id"])
        exact_keys(item["files"], FILE_ROLES, "Artifact files")
        record = {k: item[k] for k in ("artifact_id", "task_family_id", "agent_id")}
        record["files"] = {k: file_record(root, item["files"][k]) for k in sorted(FILE_ROLES)}
        record["input_sha256"] = digest(record)
        artifacts.append(record)
    manifest = {"version": VERSION, "condition_id": spec["condition_id"], "split": spec["split"],
                "proof_visibility": VISIBILITY, "judge_configuration": dict(config), "artifacts": artifacts}
    manifest["manifest_sha256"] = digest(manifest)
    return manifest


def verify_manifest(manifest, root):
    exact_keys(manifest, {"version", "condition_id", "split", "proof_visibility", "judge_configuration", "artifacts", "manifest_sha256"}, "Manifest")
    require(manifest["version"] == VERSION, "Unsupported version")
    require(manifest["manifest_sha256"] == digest({k: v for k, v in manifest.items() if k != "manifest_sha256"}), "Manifest hash mismatch")
    spec = {k: manifest[k] for k in ("condition_id", "split", "proof_visibility", "judge_configuration")}
    spec["artifacts"] = []
    for item in manifest["artifacts"]:
        exact_keys(item, {"artifact_id", "task_family_id", "agent_id", "files", "input_sha256"}, "Frozen artifact")
        spec["artifacts"].append({**{k: item[k] for k in ("artifact_id", "task_family_id", "agent_id")},
                                  "files": {k: v["path"] for k, v in item["files"].items()}})
    require(freeze_manifest(spec, root) == manifest, "Input bytes or frozen metadata changed")


def parse_prediction(raw):
    """Require one JSON object and exact decimal unit mass; never extract, clip, or normalize."""
    require(isinstance(raw, str) and len(raw.encode()) <= MAX_RESPONSE_BYTES, "Invalid response text/size")
    value = load_json(raw, decimal=True)
    exact_keys(value, {"probabilities", "rationale"}, "Forecast")
    require(isinstance(value["rationale"], str), "Rationale must be text")
    q = value["probabilities"]
    require(isinstance(q, list) and len(q) == 6, "Expected six probabilities")
    require(all(type(x) in (int, Decimal) and Decimal(x).is_finite() and 0 <= x <= 1 for x in q), "Invalid probability")
    # Exact decimal arithmetic avoids accepting or repairing a rounded non-unit vector.
    # Decimal context precision must cover the supplied digits, including exponents.
    from decimal import localcontext
    with localcontext() as context:
        context.prec = MAX_RESPONSE_BYTES * 2
        require(sum((Decimal(x) for x in q), Decimal(0)) == 1, "Probabilities must sum exactly to one")
    out = [float(x) for x in q]
    require(all(x == 0 or y > 0 for x, y in zip(q, out)), "Probability underflows float representation")
    return out


def response_receipt(manifest, responses):
    """One supplied response per scheduled artifact; missing/failed responses remain rows."""
    require(isinstance(responses, list) and len(responses) <= len(manifest["artifacts"]), "Invalid response count")
    scheduled = {x["artifact_id"]: x for x in manifest["artifacts"]}
    indexed = {}
    for item in responses:
        require(isinstance(item, dict), "Response envelope must be an object")
        payload = "response" if "response" in item else "error"
        exact_keys(item, {"artifact_id", "input_sha256", "manifest_sha256", payload}, "Response envelope")
        key = item["artifact_id"]
        require(isinstance(key, str) and key in scheduled and key not in indexed, "Unknown/duplicate response ID")
        require(item["input_sha256"] == scheduled[key]["input_sha256"], "Response input hash mismatch")
        require(item["manifest_sha256"] == manifest["manifest_sha256"], "Response condition hash mismatch")
        require(isinstance(item[payload], str), "Response/error must be text")
        if payload == "error":
            nonempty_string(item[payload], "Error category")
        indexed[key] = item
    records = []
    for key, item in scheduled.items():
        record = {"artifact_id": key, "input_sha256": item["input_sha256"], "status": "missing"}
        if key in indexed:
            supplied = indexed[key]
            if "error" in supplied:
                record.update(status="error", error=supplied["error"])
            else:
                raw = supplied["response"]
                record["response_sha256"] = hashlib.sha256(raw.encode()).hexdigest()
                try:
                    record.update(status="ok", probabilities=parse_prediction(raw))
                except (ValueError, TypeError, ArithmeticError, RecursionError):
                    record.update(status="invalid", error="invalid_probability_json")
        records.append(record)
    return {"manifest_sha256": manifest["manifest_sha256"], "responses_sha256": digest(responses), "records": records}


def artifact_metrics(q, ratings):
    """Compute proper scores per observation and distances to the noisy empirical histogram."""
    count = len(ratings)
    require(count > 0, "Cannot score an artifact without ratings")
    p = [ratings.count(r) / count for r in range(6)]
    cdf_q = [math.fsum(q[:c + 1]) for c in range(5)]
    cdf_p = [math.fsum(p[:c + 1]) for c in range(5)]
    rps = math.fsum(math.fsum((cdf_q[c] - (r <= c)) ** 2 for c in range(5)) / 5 for r in ratings) / count
    brier = math.fsum(math.fsum((q[c] - (r == c)) ** 2 for c in range(6)) for r in ratings) / count
    ce = math.inf if any(q[r] == 0 for r in ratings) else math.fsum(-math.log(q[r]) for r in ratings) / count
    entropy = -math.fsum(x * math.log(x) for x in p if x > 0)
    human_mean = math.fsum(ratings) / count / 5
    judge_mean = math.fsum(c * q[c] for c in range(6)) / 5
    return {"rps": rps, "ce": ce, "brier": brier, "kl_human_to_judge": ce - entropy,
            "tvd": 0.5 * math.fsum(abs(a - b) for a, b in zip(q, p)),
            "human_entropy": entropy,
            "empirical_cdf_squared_distance": math.fsum((a - b) ** 2 for a, b in zip(cdf_q, cdf_p)) / 5,
            "empirical_disagreement": math.fsum(x * (1 - x) for x in cdf_p) / 5,
            "squared_mean_error": (judge_mean - human_mean) ** 2,
            "mae": abs(judge_mean - human_mean), "bias": judge_mean - human_mean,
            "judge_mean": judge_mean, "human_mean": human_mean,
            "zero_probability_ratings": sum(q[r] == 0 for r in ratings)}


def pearson(x, y):
    if len(x) < 2:
        return None
    mx, my = math.fsum(x) / len(x), math.fsum(y) / len(y)
    dx, dy = [a - mx for a in x], [a - my for a in y]
    denominator = math.sqrt(math.fsum(a * a for a in dx) * math.fsum(b * b for b in dy))
    return math.fsum(a * b for a, b in zip(dx, dy)) / denominator if denominator else None


def correlations(x, y):
    result = {"pearson": pearson(x, y), "spearman": None, "kendall_tau_b": None}
    if result["pearson"] is None:
        return result, {"status": "undefined: fewer than two artifacts or zero variance", "scipy_version": None}
    try:
        import scipy
        from scipy.stats import kendalltau, spearmanr
    except (ImportError, OSError):
        return result, {"status": "unavailable: SciPy not installed or not loadable", "scipy_version": None}
    result["spearman"] = float(spearmanr(x, y).statistic)
    result["kendall_tau_b"] = float(kendalltau(x, y, variant="b").statistic)
    require(all(math.isfinite(v) for v in result.values()), "Unexpected nonfinite correlation")
    return result, {"status": "computed; Spearman average ranks and Kendall tau-b ties", "scipy_version": scipy.__version__}


def json_safe(value):
    """Standard JSON has no infinity token; retain its meaning as the explicit string Infinity."""
    if isinstance(value, float) and math.isinf(value):
        return "Infinity" if value > 0 else "-Infinity"
    if isinstance(value, dict):
        return {k: json_safe(v) for k, v in value.items()}
    if isinstance(value, list):
        return [json_safe(v) for v in value]
    return value


def evaluate(manifest, responses, ratings, root):
    verify_manifest(manifest, root)
    receipt = response_receipt(manifest, responses)
    scheduled = {x["artifact_id"]: x for x in manifest["artifacts"]}
    require(isinstance(ratings, list) and len(ratings) <= MAX_RATINGS, "Invalid rating count")
    grouped, seen = {key: [] for key in scheduled}, set()
    for row in ratings:
        exact_keys(row, {"artifact_id", "input_sha256", "rater_id", "rating"}, "Rating")
        key = row["artifact_id"]
        require(isinstance(key, str) and key in scheduled, "Unknown rating artifact")
        require(row["input_sha256"] == scheduled[key]["input_sha256"], "Rating input hash mismatch")
        nonempty_string(row["rater_id"], "Rater ID")
        pair = key, row["rater_id"]
        require(pair not in seen, "Duplicate artifact/rater observation")
        seen.add(pair)
        require(type(row["rating"]) is int and 0 <= row["rating"] <= 5, "Rating must be an integer 0–5")
        grouped[key].append(row["rating"])
    scored = [artifact_metrics(row["probabilities"], grouped[row["artifact_id"]])
              for row in receipt["records"] if row["status"] == "ok" and grouped[row["artifact_id"]]]
    n, k = len(scheduled), len(scored)
    means = {key: math.fsum(x[key] for x in scored) / k for key in scored[0] if key != "zero_probability_ratings"} if k else None
    correlation_status = {"status": "not computed: no scored artifacts", "scipy_version": None}
    if means:
        means["nrmse"] = math.sqrt(means["squared_mean_error"])
        means["root_mean_cdf_distance"] = math.sqrt(means["empirical_cdf_squared_distance"])
        corr, correlation_status = correlations([x["judge_mean"] for x in scored], [x["human_mean"] for x in scored])
        means.update(corr)
    bounds = {}
    for metric, upper in {"rps": 1, "brier": 2, "ce": math.inf, "tvd": 1, "empirical_cdf_squared_distance": 1, "squared_mean_error": 1}.items():
        observed = math.fsum(x[metric] for x in scored)
        bounds[metric] = {"lower": observed / n, "upper": (observed + (n - k) * upper) / n if n > k else observed / n}
    for source, target in (("squared_mean_error", "nrmse"), ("empirical_cdf_squared_distance", "root_mean_cdf_distance")):
        bounds[target] = {name: math.sqrt(value) for name, value in bounds[source].items()}
    statuses = Counter(x["status"] for x in receipt["records"])
    report = {"version": VERSION, "metrics_version": METRICS_VERSION, "manifest_sha256": manifest["manifest_sha256"],
              "condition_id": manifest["condition_id"], "split": manifest["split"],
              "ratings_sha256": digest(ratings), "forecast_receipt_sha256": digest(receipt),
              "counts": {"scheduled_artifacts": n, "response_statuses": {s: statuses[s] for s in ("ok", "invalid", "error", "missing")},
                         "rated_artifacts": sum(bool(v) for v in grouped.values()), "individual_ratings": len(ratings),
                         "unrated_artifacts": sum(not v for v in grouped.values()),
                         "scored_artifacts": k, "unscored_artifacts": n - k,
                         "zero_probability_ratings_scored": sum(x["zero_probability_ratings"] for x in scored)},
              "scored_artifacts_only": means, "full_denominator_bounds": bounds,
              "point_estimates_cover_full_manifest": k == n,
              "uncertainty": "Not computed; bounds describe missingness, not confidence intervals.",
              "pearson_undefined_policy": "null for fewer than two scored artifacts or zero variance",
              "rank_correlations": correlation_status,
              "forecast_receipt": receipt}
    return json_safe(report)


def read(path):
    path = Path(path)
    require(path.stat().st_size <= MAX_JSON_BYTES, "JSON file too large")
    return load_json(path.read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    freeze = commands.add_parser("freeze")
    freeze.add_argument("--spec", required=True)
    score = commands.add_parser("evaluate")
    for name in ("manifest", "responses", "ratings"):
        score.add_argument("--" + name, required=True)
    for command in (freeze, score):
        command.add_argument("--input-root", required=True)
        command.add_argument("--out", required=True)
    args = parser.parse_args()
    if args.command == "freeze":
        result = freeze_manifest(read(args.spec), args.input_root)
    else:
        result = evaluate(read(args.manifest), read(args.responses), read(args.ratings), args.input_root)
    # Never overwrite an existing receipt. Inputs and outputs may be private.
    with Path(args.out).open("x") as stream:
        stream.write(json.dumps(result, indent=2, ensure_ascii=False, allow_nan=False) + "\n")
    print("Wrote new offline " + args.command + " receipt; no model call was made.")


if __name__ == "__main__":
    main()
