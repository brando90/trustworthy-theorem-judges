"""TLDR: Independently reconstruct trained forecasts, preprocessing, metrics and stored uncertainty."""

import argparse
import hashlib
import json
import math
import warnings
from pathlib import Path

import numpy as np
from scipy.stats import kendalltau, pearsonr, spearmanr


GRID = np.arange(6, dtype=float) / 5
METRICS = ("ce", "kl", "entropy", "brier", "rps", "weighted_pmf", "tvd",
           "mae", "bias", "human_mean", "judge_mean", "pearson", "spearman", "kendall")
METHODS = ("mixture_weighted_pmf", "mixture_pearson", "softmax_weighted_pmf",
           "softmax_ce", "softmax_brier", "softmax_rps", "constant")


def load(path):
    return json.loads(Path(path).read_text())


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def close(actual, expected, label, atol=2e-9, rtol=2e-8):
    if expected is None:
        assert actual is None or not np.isfinite(actual), (label, actual, expected)
        return
    if actual is None:
        assert not np.isfinite(expected), (label, actual, expected)
        return
    assert np.allclose(actual, expected, atol=atol, rtol=rtol, equal_nan=True), (label, actual, expected)


def histogram(values):
    result = np.zeros(6)
    assert len(values)
    for value in values:
        assert float(value).is_integer() and 0 <= value <= 5
        result[int(value)] += 1 / len(values)
    return result


def smoothing(q, epsilon):
    return np.asarray(q) * (1 - 6 * epsilon) + epsilon


def probabilities(logits):
    shifted = logits - np.max(logits, axis=1, keepdims=True)
    exp = np.exp(shifted)
    return exp / exp.sum(axis=1, keepdims=True)


def correlations(a, b):
    centered_a, centered_b = a - a.mean(), b - b.mean()
    if np.sqrt(np.sum(centered_a ** 2) * np.sum(centered_b ** 2)) <= 1e-25:
        return {key: float("nan") for key in ("pearson", "spearman", "kendall")}
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        return {"pearson": float(pearsonr(a, b)[0]),
                "spearman": float(spearmanr(a, b)[0]),
                "kendall": float(kendalltau(a, b)[0])}


def metrics(p, q):
    assert p.shape == q.shape and p.ndim == 2 and p.shape[1] == 6
    assert np.isfinite(p).all() and np.isfinite(q).all() and np.min(q) > 0
    close(q.sum(axis=1), np.ones(len(q)), "forecast normalization", atol=1e-12, rtol=0)
    target_mean = np.round(p @ GRID, 12)
    forecast_mean = np.round(q @ GRID, 12)
    entropy_per_row = -np.sum(p * np.log(np.maximum(p, 1e-300)), axis=1)
    log_loss = -np.sum(p * np.log(q), axis=1)
    cumulative_p, cumulative_q = np.cumsum(p, axis=1)[:, :5], np.cumsum(q, axis=1)[:, :5]
    values = {
        "ce": float(log_loss.mean()), "kl": float((log_loss - entropy_per_row).mean()),
        "entropy": float(entropy_per_row.mean()),
        "brier": float(np.mean(np.sum(q * q - 2 * p * q, axis=1) + 1)),
        "rps": float(np.mean(cumulative_q ** 2 - 2 * cumulative_q * cumulative_p + cumulative_p)),
        "weighted_pmf": float(np.mean(np.sum(p * (p - q) ** 2, axis=1))),
        "tvd": float(np.mean(np.sum(np.abs(p - q), axis=1) / 2)),
        "mae": float(np.mean(np.abs(forecast_mean - target_mean))),
        "bias": float(np.mean(forecast_mean - target_mean)),
        "human_mean": float(target_mean.mean()), "judge_mean": float(forecast_mean.mean()),
    }
    values.update(correlations(forecast_mean, target_mean))
    return values


def quantile(values, probability):
    values = sorted(float(x) for x in values if x is not None and np.isfinite(x))
    if not values:
        return None
    position = (len(values) - 1) * probability
    lower, upper = math.floor(position), math.ceil(position)
    return values[lower] + (values[upper] - values[lower]) * (position - lower)


def interval_check(receipt, values, label):
    finite = [x for x in values if x is not None and np.isfinite(x)]
    close(quantile(finite, .025), receipt["lo"], label + " lower")
    close(quantile(finite, .975), receipt["hi"], label + " upper")
    assert len(finite) == receipt["valid_draws"], (label, len(finite), receipt["valid_draws"])
    if "invalid_draws" in receipt:
        assert len(values) - len(finite) == receipt["invalid_draws"], label


def original_partitions(rows, seeds):
    families = sorted({row["family"] for row in rows})
    answer = []
    for seed in seeds:
        order = np.random.default_rng(seed).permutation(families)
        allocation = {family: index % 5 for index, family in enumerate(order)}
        outer = np.asarray([allocation[row["family"]] for row in rows])
        inner = []
        for fold in range(5):
            other_families = [family for family in order if allocation[family] != fold]
            inner.append({family: index % 4 for index, family in enumerate(other_families)})
        answer.append((outer, inner))
    return answer


def softmax_prediction(model, x):
    mean, sd, weights = (np.asarray(model[key]) for key in ("mean", "sd", "weights"))
    design = np.column_stack([np.ones(len(x)), (x - mean) / sd])
    return probabilities(design @ weights)


def preprocess_check(model, train_x, label):
    close(np.asarray(model["mean"]), train_x.mean(axis=0), label + " mean", atol=1e-12, rtol=0)
    close(np.asarray(model["sd"]), np.maximum(train_x.std(axis=0), 1e-8), label + " scale", atol=1e-12, rtol=0)
    weights = np.asarray(model["weights"])
    close(weights.sum(axis=1), np.zeros(len(weights)), label + " centered coefficients", atol=1e-12, rtol=0)
    assert weights.shape == (train_x.shape[1] + 1, 6)
    if "coordinates" in model:
        basis = np.zeros((6, 5))
        for k in range(1, 6):
            basis[:k, k - 1] = 1 / np.sqrt(k * (k + 1))
            basis[k, k - 1] = -k / np.sqrt(k * (k + 1))
        close(np.asarray(model["coordinates"]) @ basis.T, weights, label + " reduced coefficients")


def training_loss(p, q, loss):
    if loss == "weighted_pmf":
        return float(np.mean(np.sum(p * (p - q) ** 2, axis=1)))
    if loss == "brier":
        return float(np.mean(1 + np.sum(q * q - 2 * p * q, axis=1)))
    if loss == "rps":
        cp, cq = np.cumsum(p, axis=1)[:, :5], np.cumsum(q, axis=1)[:, :5]
        return float(np.mean(cq * cq - 2 * cp * cq + cp))
    assert loss == "ce"
    return float(-np.mean(np.sum(p * np.log(q), axis=1)))


def mixture_certificate(q, p, weights, objective):
    forecast = np.sum(q * weights[None, :, None], axis=1)
    if objective == "weighted_pmf":
        gradient = 2 * np.mean(np.sum(p[:, None, :] * (forecast - p)[:, None, :] * q, axis=2), axis=0)
        gap = float(gradient @ weights - np.min(gradient))
        return gap <= 1e-8, {"simplex_gap": gap}
    assert objective == "pearson"
    means, target = q @ GRID, p @ GRID
    a, b = means - means.mean(axis=0), target - target.mean()
    column_norms, target_norm = np.linalg.norm(a, axis=0), np.linalg.norm(b)
    active = column_norms > 1e-12
    if target_norm <= 1e-12 or not np.any(active):
        return True, {"undefined_target_or_all_constant": True}
    unit = a[:, active] / column_norms[active]
    scalar_products = unit.T @ b
    z = a @ weights
    if np.linalg.norm(z) <= 1e-12:
        return False, {"unexpected_constant_forecast": True}
    observed = float(z @ b / (np.linalg.norm(z) * target_norm))
    if max(scalar_products) <= 0:
        optimum = float(max(scalar_products) / target_norm)
        return abs(observed - optimum) <= 1e-8, {"vertex_gap": abs(observed - optimum)}
    scale = float(z @ b / (z @ z))
    projected = scale * z
    gradient = unit.T @ (projected - b)
    coefficients = scale * weights[active] * column_norms[active]
    dual = max(0.0, float(-gradient.min())) / (1 + target_norm)
    complementarity = float(np.max(np.abs(coefficients * gradient))) / (1 + target_norm ** 2)
    orthogonality = abs(float(projected @ (b - projected))) / (1 + target_norm ** 2)
    identity = abs(observed - float(np.linalg.norm(projected) / target_norm))
    residual = max(dual, complementarity, orthogonality, identity)
    return bool(scale > 0 and residual <= 1e-8), {"cone_certificate_residual": residual}


def verify(data_path, out, private_out, protocol_path):
    cfg, data = load(protocol_path), load(data_path)
    results = load(out / "results.json")
    saved = load(private_out / "forecasts.json")
    bootstrap = load(private_out / "bootstrap.json")
    assert results["dataset_sha256"] == cfg["dataset_sha256"] == sha256(data_path)
    assert results["protocol_sha256"] == sha256(protocol_path)
    rows, candidates = data["rows"], cfg["candidate_order"]
    n, seed_count = len(rows), len(cfg["seeds"])
    assert n == 75 and len({r["task"] for r in rows}) == 25 and len({r["family"] for r in rows}) == 19
    assert sum(len(r["ratings"]) for r in rows) == 195
    p = np.asarray([histogram(row["ratings"]) for row in rows])
    raw = np.asarray([[histogram(values) for values in data["outputs"][name]] for name in candidates])
    q_candidates = smoothing(raw.transpose(1, 0, 2), cfg["epsilon"])
    x = np.column_stack([np.mean(data["outputs"][name], axis=1) / 5 for name in candidates])
    partitions = original_partitions(rows, cfg["seeds"])
    assert len(saved["partitions"]) == len(partitions)
    for index, ((outer, inner), recorded) in enumerate(zip(partitions, saved["partitions"])):
        assert np.array_equal(outer, recorded["outer"]), ("partition", index)
        assert inner == recorded["inner"], ("inner partition", index)

    assert set(results["methods"]) == set(METHODS) == set(saved["outputs"])
    outputs = {method: np.asarray(saved["outputs"][method]) for method in METHODS}
    reconstructed = {method: np.full((seed_count, n, 6), np.nan) for method in METHODS}
    covered = {method: np.zeros((seed_count, n), dtype=int) for method in METHODS}
    for entry in saved["models"]:
        method, seed_index, fold, model = entry["method"], entry["seed_index"], entry["fold"], entry["model"]
        outer = partitions[seed_index][0]
        train, test = np.asarray(entry["train_indices"]), np.asarray(entry["test_indices"])
        assert np.array_equal(train, np.flatnonzero(outer != fold))
        assert np.array_equal(test, np.flatnonzero(outer == fold))
        assert not ({rows[i]["family"] for i in train} & {rows[i]["family"] for i in test})
        if method.startswith("mixture_"):
            weights = np.asarray(model["weights"])
            assert weights.shape == (len(candidates),) and np.min(weights) >= -1e-10
            close(weights.sum(), 1.0, "simplex weights", atol=1e-10, rtol=0)
            predicted = np.sum(q_candidates[test] * weights[None, :, None], axis=1)
        elif method.startswith("softmax_"):
            preprocess_check(model, x[train], method)
            predicted = smoothing(softmax_prediction(model, x[test]), cfg["epsilon"])
        else:
            assert method == "constant"
            expected = smoothing(p[train].mean(axis=0), cfg["epsilon"])
            close(np.asarray(model["pmf"]), expected, "training-only constant")
            predicted = np.broadcast_to(expected, (len(test), 6))
        reconstructed[method][seed_index, test] = predicted
        covered[method][seed_index, test] += 1
    for method in METHODS:
        assert outputs[method].shape == (seed_count, n, 6)
        assert np.all(covered[method] == 1), method
        assert np.isfinite(reconstructed[method]).all()
        close(reconstructed[method], outputs[method], method + " complete forecasts", atol=2e-11, rtol=2e-10)
    assert len(saved["models"]) == len(METHODS) * 5 * seed_count

    public_fits = results["softmax_fits"]
    assert len(public_fits) == len(saved["softmax_fit_models"]) == cfg["expected_softmax_fits"]
    assert {entry["public_fit_index"] for entry in saved["softmax_fit_models"]} == set(range(len(public_fits)))
    softmax_by_key = {}
    for entry in saved["softmax_fit_models"]:
        receipt, model = public_fits[entry["public_fit_index"]], entry["model"]
        train = np.asarray(entry["train_indices"])
        assert len(set(train.tolist())) == len(train) and np.min(train) >= 0 and np.max(train) < n
        seed_index, fold, inner_fold = receipt["seed_index"], receipt["fold"], receipt["inner_fold"]
        outer, inner = partitions[seed_index]
        outer_train = np.flatnonzero(outer != fold)
        expected_train = (outer_train if inner_fold is None else
                          outer_train[[inner[fold][rows[i]["family"]] != inner_fold for i in outer_train]])
        assert np.array_equal(train, expected_train), ("fit training membership", entry["public_fit_index"])
        expected_seed = cfg["seeds"][seed_index] + 100 * fold + (99 if inner_fold is None else inner_fold)
        assert receipt["seed"] == expected_seed
        assert receipt["method"] == "softmax_" + model["loss"] and receipt["loss"] == model["loss"]
        assert model["strength"] == receipt["strength"] and receipt["strength"] in cfg["l2_strengths"]
        key = (receipt["method"], seed_index, fold, inner_fold, receipt["strength"])
        assert key not in softmax_by_key
        softmax_by_key[key] = entry
        for option, value in cfg["softmax_optimizer"].items():
            assert receipt["optimizer_options"][option] == value
        preprocess_check(model, x[train], "fit " + str(entry["public_fit_index"]))
        q = softmax_prediction(model, x[train])
        assert receipt["finite"] == bool(np.isfinite(q).all() and np.isfinite(model["weights"]).all())
        assert receipt["finite"] and isinstance(receipt["success"], bool)
        data_loss = training_loss(p[train], q, model["loss"])
        penalty = float(model["strength"] * np.sum(np.asarray(model["weights"]) ** 2) / 2)
        close(data_loss, receipt["data_loss"], "fit data loss")
        close(penalty, receipt["penalty"], "fit penalty")
        close(data_loss + penalty, receipt["objective"], "fit objective")
        assert receipt["training_rows"] == len(train)
        assert receipt["optimized_parameters"] == (x.shape[1] + 1) * 5
        assert receipt["stored_coefficients"] == (x.shape[1] + 1) * 6

    mixture_fits = results["mixture_fits"]
    assert len(mixture_fits) == cfg["expected_mixture_fits"]
    mixture_models = [entry for entry in saved["models"] if entry["method"].startswith("mixture_")]
    mixture_by_key = {(entry["method"], entry["seed_index"], entry["fold"]): entry for entry in mixture_models}
    certificate_count = 0
    for receipt in mixture_fits:
        method = receipt.get("method", "mixture_" + receipt["objective"])
        seed_index = receipt.get("seed_index", cfg["seeds"].index(receipt["seed"]) if "seed" in receipt else None)
        fold = receipt.get("fold", receipt.get("outer_fold"))
        entry = mixture_by_key[(method, seed_index, fold)]
        train = np.asarray(entry["train_indices"])
        valid, _ = mixture_certificate(q_candidates[train], p[train], np.asarray(entry["model"]["weights"]), method.removeprefix("mixture_"))
        assert bool(receipt["success"]) == valid, (method, seed_index, fold, receipt["success"], valid)
        certificate_count += valid
    assert len(results["softmax_choices"]) == cfg["expected_softmax_choices"]
    choice_keys = set()
    for choice in results["softmax_choices"]:
        method, seed_index, fold = choice["method"], choice["seed_index"], choice["fold"]
        key = (method, seed_index, fold)
        assert key not in choice_keys
        choice_keys.add(key)
        outer, inner = partitions[seed_index]
        outer_train = np.flatnonzero(outer != fold)
        scores = []
        for strength in cfg["l2_strengths"]:
            held = np.full((len(outer_train), 6), np.nan)
            for inner_fold in range(4):
                valid_local = np.flatnonzero([inner[fold][rows[i]["family"]] == inner_fold for i in outer_train])
                valid = outer_train[valid_local]
                fit_model = softmax_by_key[(method, seed_index, fold, inner_fold, strength)]["model"]
                held[valid_local] = smoothing(softmax_prediction(fit_model, x[valid]), cfg["epsilon"])
            assert np.isfinite(held).all()
            scores.append(training_loss(p[outer_train], held, "rps"))
        close(scores, choice["inner_rps"], "validation RPS")
        selected = min(range(len(scores)), key=lambda j: (scores[j], j))
        assert cfg["l2_strengths"][selected] == choice["strength"]
        final_model = softmax_by_key[(method, seed_index, fold, None, choice["strength"])]["model"]
        final_entry = next(entry for entry in saved["models"] if
                           (entry["method"], entry["seed_index"], entry["fold"]) == key)
        assert final_model == final_entry["model"], ("final refit identity", key)

    matrix = {}
    for method in METHODS:
        by_seed = [metrics(p, q) for q in outputs[method]]
        matrix[method] = {key: float(np.mean([s[key] for s in by_seed])) for key in METRICS}
        for key in METRICS:
            close(matrix[method][key], results["matrix"][method][key], method + ": " + key)
            if "per_seed" in results:
                for index in range(seed_count):
                    close(by_seed[index][key], results["per_seed"][method][index][key], method + " per-seed " + key)
            close(float(np.std([s[key] for s in by_seed], ddof=1)),
                  results["resplit_standard_deviations"][method][key], method + " resplit SD " + key)
        for metric, samples in bootstrap["conditional"][method].items():
            assert len(samples) == cfg["bootstrap_draws"]
            interval_check(results["conditional_intervals"][method][metric], samples, method + " " + metric)
    contrasts = {"mixture_weighted_minus_pearson": ("mixture_weighted_pmf", "mixture_pearson"),
                 **{"softmax_weighted_minus_" + loss: ("softmax_weighted_pmf", "softmax_" + loss)
                    for loss in ("ce", "brier", "rps")}}
    assert set(bootstrap["differences"]) == set(contrasts)
    for contrast, metric_samples in bootstrap["differences"].items():
        first, second = contrasts[contrast]
        for metric, samples in metric_samples.items():
            assert len(samples) == cfg["bootstrap_draws"]
            interval_check(results["conditional_differences"][contrast][metric], samples, contrast + " " + metric)
            close(matrix[first][metric] - matrix[second][metric],
                  results["conditional_differences"][contrast][metric]["estimate"], contrast + " estimate")
            for index, value in enumerate(samples):
                a, b = bootstrap["conditional"][first][metric][index], bootstrap["conditional"][second][metric][index]
                difference = a - b if a is not None and b is not None else None
                close(difference, value, contrast + " paired sample")
    for metric, samples in bootstrap["refit_differences"].items():
        assert len(samples) == cfg["mixture_refit_bootstrap_draws"]
        interval_check(results["mixture_refit_differences"][metric], samples, "refit " + metric)
        close(matrix["mixture_weighted_pmf"][metric] - matrix["mixture_pearson"][metric],
              results["mixture_refit_differences"][metric]["estimate"], "refit point estimate")
    assert len(bootstrap["ledger"]) == cfg["mixture_refit_bootstrap_draws"]

    families = sorted({row["family"] for row in rows})
    rng = np.random.default_rng(cfg["bootstrap_seed"])
    conditional_draws_checked = (0, cfg["bootstrap_draws"] // 2 - 1, cfg["bootstrap_draws"] - 1)
    for index, ledger in enumerate(bootstrap["ledger"]):
        draw = rng.choice(families, size=len(families), replace=True)
        selected_rows = np.asarray([i for family in draw for i, row in enumerate(rows) if row["family"] == family])
        assert ledger["draw"] == index and ledger["unique_families"] == len(set(draw))
        if ledger["valid"]:
            expected_fits = 2 * sum(np.any(outer[selected_rows] == fold)
                                    for outer, _ in partitions for fold in range(5))
            assert ledger["fits"] == expected_fits and ledger["certificate_failures"] == 0
            assert ledger["reason"] is None
        if index in conditional_draws_checked:
            for method in METHODS:
                sample_metrics = [metrics(p[selected_rows], q[selected_rows]) for q in outputs[method]]
                for metric in METRICS:
                    value = float(np.mean([row[metric] for row in sample_metrics]))
                    close(value, bootstrap["conditional"][method][metric][index], "conditional sample reconstruction")

    expected_counts = {"artifacts": n, "tasks": 25, "families": 19, "expert_ratings": 195,
                       "mixture_fits": len(mixture_fits), "softmax_fits": len(public_fits),
                       "softmax_choices": len(results["softmax_choices"]), "final_models": len(saved["models"]),
                       "artifact_forecasts": len(METHODS) * seed_count * n,
                       "softmax_nonconverged": sum(not row["success"] for row in public_fits),
                       "mixture_refit_bootstrap_draws": len(bootstrap["ledger"]),
                       "mixture_refit_invalid_draws": sum(not row["valid"] for row in bootstrap["ledger"]),
                       "mixture_bootstrap_fits": sum(row["fits"] for row in bootstrap["ledger"])}
    assert results["counts"] == expected_counts, (results["counts"], expected_counts)
    assert results["new_inference_calls"] == cfg["new_inference_calls"] == 0
    assert results["provider_cost_usd"] == cfg["provider_cost_usd"] == 0

    return {"status": "PASS", "dataset_sha256": sha256(data_path),
            "protocol_sha256": sha256(protocol_path), "results_sha256": sha256(out / "results.json"),
            "verifier_sha256": sha256(__file__), "reconstructed_forecast_rows": len(METHODS) * seed_count * n,
            "reconstructed_final_models": len(saved["models"]), "verified_softmax_preprocessing": len(public_fits),
            "softmax_nonconverged_fits": sum(not entry["success"] for entry in public_fits),
            "mixture_certificates_passed": int(certificate_count), "mixture_fits": len(mixture_fits),
            "methods": list(METHODS), "bootstrap_draws": cfg["bootstrap_draws"],
            "mixture_refit_bootstrap_draws": cfg["mixture_refit_bootstrap_draws"],
            "conditional_draws_independently_reconstructed": list(conditional_draws_checked),
            "independent_metrics": list(METRICS), "new_model_calls": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--private-out", type=Path, required=True)
    parser.add_argument("--protocol", type=Path, default=Path(__file__).resolve().parents[1] / "protocol.json")
    args = parser.parse_args()
    report = verify(args.data, args.out, args.private_out, args.protocol)
    (args.out / "verification.json").write_text(json.dumps(report, indent=2, allow_nan=False) + "\n")
    print(json.dumps(report, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
