#!/usr/bin/env python3
"""Train on training forecasts, select on validation, evaluate test once."""
import argparse
from collections import Counter
import math
import warnings

import numpy as np
from scipy.optimize import minimize
from scipy.special import expit, logit
from scipy.stats import kendalltau, pearsonr, spearmanr

from forecast import ROOT, atomic_json, encoded, load_inputs, read_json, sha, verify_freeze

EPS = 1e-6
RIDGES = (0.01, 0.1, 1.0, 10.0)
METRICS = ("brier", "log_loss", "mean_absolute_error", "bias", "mean_prediction", "mean_label",
           "pearson", "spearman", "kendall", "auroc", "accuracy", "precision", "recall", "cohen_kappa")


def losses(y, p):
    q = np.clip(p, EPS, 1 - EPS)
    return (p - y) ** 2, -(y * np.log(q) + (1 - y) * np.log1p(-q))


def metrics(y, p):
    y, p = np.asarray(y), np.asarray(p)
    if len(y) == 0:
        return {k: None for k in METRICS}
    brier, ce = losses(y, p)
    result = {"brier": float(np.mean(brier)), "log_loss": float(np.mean(ce)),
              "mean_absolute_error": float(np.mean(abs(p - y))), "bias": float(np.mean(p - y)),
              "mean_prediction": float(np.mean(p)), "mean_label": float(np.mean(y))}
    for name, fn in (("pearson", pearsonr), ("spearman", spearmanr), ("kendall", kendalltau)):
        if len(y) < 2 or np.ptp(y) == 0 or np.ptp(p) == 0:
            result[name] = None
        else:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                v = float(fn(y, p).statistic)
            result[name] = v if math.isfinite(v) else None
    pos, neg = p[y == 1], p[y == 0]
    result["auroc"] = float(np.mean((pos[:, None] > neg).astype(float) + 0.5 * (pos[:, None] == neg))) if len(pos) and len(neg) else None
    prediction = p >= 0.5
    tp, tn = int(np.sum(prediction & (y == 1))), int(np.sum(~prediction & (y == 0)))
    fp, fn = int(np.sum(prediction & (y == 0))), int(np.sum(~prediction & (y == 1)))
    result.update(accuracy=(tp + tn) / len(y), precision=tp / (tp + fp) if tp + fp else None,
                  recall=tp / (tp + fn) if tp + fn else None,
                  confusion={"tp": tp, "tn": tn, "fp": fp, "fn": fn})
    chance = float(np.mean(prediction) * np.mean(y) + (1 - np.mean(prediction)) * (1 - np.mean(y)))
    result["cohen_kappa"] = (result["accuracy"] - chance) / (1 - chance) if chance < 1 else None
    return result


def fit_mapping(p, y, loss, ridge):
    # Convex CE and low-dimensional Brier fits: fixed exhaustive start set, fixed bounds.
    x = logit(np.clip(p, EPS, 1 - EPS))
    def objective(theta):
        a, b = theta
        q = expit(a + b * x)
        bs, ce = losses(y, q)
        return float(np.mean(ce if loss == "ce" else bs) + ridge * (a * a + (b - 1) ** 2))
    attempts = []
    for initial in ((0, 0), (0, 1), (0, 2)):
        fit = minimize(objective, initial, method="L-BFGS-B", bounds=((-8, 8), (0, 5)),
                       options={"maxiter": 500, "ftol": 1e-12, "gtol": 1e-8})
        attempts.append({"a": float(fit.x[0]), "b": float(fit.x[1]), "objective": float(fit.fun), "success": bool(fit.success)})
    acceptable = [a for a in attempts if a["success"] and math.isfinite(a["objective"])]
    if not acceptable:
        return {"loss": loss, "ridge": ridge, "status": "optimizer_failed", "attempts": attempts}
    best = min(acceptable, key=lambda a: (a["objective"], a["a"], a["b"]))
    return {"loss": loss, "ridge": ridge, "status": "fit", **best, "attempts": attempts}


def map_probs(p, missing, mapping):
    if mapping["status"] != "fit":
        return np.full(len(p), 0.5)
    result = expit(mapping["a"] + mapping["b"] * logit(np.clip(p, EPS, 1 - EPS)))
    result[missing] = 0.5
    return result


def get_data(labels, receipt_by_id, split):
    selected = [r for r in labels if r["split"] == split and r["label"] in (0, 1) and r["label"] is not None]
    y = np.array([r["label"] for r in selected], dtype=float)
    valid = np.array([receipt_by_id.get(r["id"], {}).get("status") == "forecast" for r in selected], dtype=bool)
    p = np.array([receipt_by_id[r["id"]]["probability"] if ok else 0.5 for r, ok in zip(selected, valid)], dtype=float)
    families = np.array([r["family"] for r in selected])
    return selected, y, p, ~valid, families


def select():
    verify_freeze()
    path = ROOT / "results/selection.json"
    if path.exists():
        raise RuntimeError("Selection already fixed; verify/recompute in a separate output, never refit")
    _, labels = load_inputs()
    receipts = read_json(ROOT / "results/forecasts.json")["receipts"]
    by_id = {r["id"]: r for r in receipts if r["kind"] == "primary"}
    prior = [by_id[r["id"]] for r in labels if r["split"] in {"train", "validation"}]
    assert not any(r["id"] in by_id for r in labels if r["split"] == "test"), "Test calls preceded selection"
    _, ty, tp, tm, _ = get_data(labels, by_id, "train")
    _, vy, vp, vm, _ = get_data(labels, by_id, "validation")
    result = {"inference_freeze_sha256": sha((ROOT / "inference_freeze.json").read_bytes()),
              "training_validation_receipts_sha256": sha(encoded(prior)),
              "constant": float(np.mean(ty)), "train_eligible": len(ty), "train_valid": int(sum(~tm)),
              "validation_eligible": len(vy), "validation_valid": int(sum(~vm)),
              "candidates": {}, "selected": {}}
    assert len(ty) and len(vy)
    for loss in ("ce", "brier"):
        candidates = []
        if np.sum(~tm) >= 2 and np.ptp(ty[~tm]) > 0:
            for ridge in RIDGES:
                mapping = fit_mapping(tp[~tm], ty[~tm], loss, ridge)
                if mapping["status"] == "fit":
                    q = map_probs(vp, vm, mapping)
                    mapping["validation_metrics"] = metrics(vy, q)
                    mapping["selection_loss"] = mapping["validation_metrics"]["log_loss" if loss == "ce" else "brier"]
                candidates.append(mapping)
        result["candidates"][loss] = candidates
        fitted = [m for m in candidates if m["status"] == "fit"]
        if fitted:
            best = min(m["selection_loss"] for m in fitted)
            ties = [m for m in fitted if m["selection_loss"] <= best + 1e-12]
            result["selected"][loss] = max(ties, key=lambda m: m["ridge"])
        else:
            result["selected"][loss] = {"status": "insufficient_training_outputs", "loss": loss}
    import time
    result["selected_unix"] = time.time()
    atomic_json(path, result)
    print("Selection saved before test: " + sha(path.read_bytes()))


def bootstrap(y, predictions, families):
    """Family-cluster percentile intervals; two clusters only, explicitly exploratory."""
    rng = np.random.default_rng(20261109)
    unique = np.unique(families)
    values = {name: {metric: [] for metric in METRICS} for name in predictions}
    deltas = {name: {m: [] for m in ("brier", "log_loss")} for name in predictions if name != "constant"}
    for _ in range(2000):
        draw = rng.choice(unique, len(unique), replace=True)
        idx = np.concatenate([np.flatnonzero(families == f) for f in draw])
        bs = {}
        for name, p in predictions.items():
            ms = metrics(y[idx], p[idx]); bs[name] = ms
            for metric in METRICS:
                if ms[metric] is not None:
                    values[name][metric].append(ms[metric])
        for name in deltas:
            for m in deltas[name]:
                deltas[name][m].append(bs[name][m] - bs["constant"][m])
    def intervals(source):
        return {n: {m: {"interval95": [float(x) for x in np.quantile(v, [0.025, 0.975])] if v else None,
                        "defined_draws": len(v)} for m, v in ms.items()} for n, ms in source.items()}
    return {"draws": 2000, "seed": 20261109, "unit": "task/representation family", "clusters": len(unique),
            "limitation": "Only two held-out families; percentile intervals cannot establish population generalization.",
            "p_value": None, "p_value_reason": "Descriptive constructed feasibility set; no population hypothesis test prespecified.",
            "metrics": intervals(values), "paired_difference_from_constant": intervals(deltas)}


def evaluate(output=None):
    verify_freeze()
    _, labels = load_inputs()
    all_receipts = read_json(ROOT / "results/forecasts.json")["receipts"]
    by_id = {r["id"]: r for r in all_receipts if r["kind"] == "primary"}
    assert len(by_id) == len(labels), "All fixed primary calls need terminal receipts"
    selection = read_json(ROOT / "results/selection.json")
    for r in labels:
        if r["split"] == "test":
            assert by_id[r["id"]]["started_unix"] >= selection["selected_unix"]
    report = {"n_declared": len(labels), "n_terminal_receipts": len(by_id),
              "inference_freeze_sha256": sha((ROOT / "inference_freeze.json").read_bytes()),
              "selection_sha256": sha((ROOT / "results/selection.json").read_bytes()), "splits": {},
              "repeatability": "One forecast per manifest row; proof-body twins have identical inputs and measure only duplicate-prompt variation.",
              "scope": "Constructed certificate-labeled feasibility controls; no natural-output or human validation."}
    values = [r["probability"] for r in by_id.values() if r["status"] == "forecast"]
    frequencies = Counter(values)
    report["output_distribution"] = {"n_probabilities": len(values),
        "histogram": {str(k): v for k, v in sorted(frequencies.items())},
        "modal_share": max(frequencies.values()) / len(values) if values else None,
        "mean_binary_entropy_nats": float(np.mean([-(p*math.log(p) if p else 0)-((1-p)*math.log1p(-p) if p < 1 else 0) for p in values])) if values else None}
    inputs, _ = load_inputs()
    twins = []
    for family in sorted({r["family"] for r in labels}):
        pair = {r["control_type"]: r for r in labels if r["family"] == family and r["control_type"] in {"oracle", "proof_body_variant"}}
        a, b = pair["oracle"]["id"], pair["proof_body_variant"]["id"]
        assert inputs[a]["statement"] == inputs[b]["statement"]
        ra, rb = by_id[a], by_id[b]
        both = ra["status"] == rb["status"] == "forecast"
        twins.append({"family": family, "ids": [a, b], "identical_input": True,
                      "statuses": [ra["status"], rb["status"]],
                      "probability_difference": rb["probability"]-ra["probability"] if both else None,
                      "two_call_sample_sd": abs(rb["probability"]-ra["probability"])/math.sqrt(2) if both else None})
    report["proof_body_twins"] = twins
    report["proof_body_twins_scope"] = "Proofs are stripped by construction. These are identical-input duplicate calls, not evidence of robustness when proof bodies are visible."
    table = []
    for split in ("train", "validation", "test"):
        selected, y, p, missing, families = get_data(labels, by_id, split)
        pred = {"raw": p, "constant": np.full(len(p), selection["constant"]),
                "ce_mapping": map_probs(p, missing, selection["selected"]["ce"]),
                "brier_mapping": map_probs(p, missing, selection["selected"]["brier"])}
        all_items = [r for r in labels if r["split"] == split]
        ineligible = [r for r in all_items if r["label"] is None]
        s = {"n_manifest": len(all_items), "n_eligible": len(y), "n_valid_eligible_forecasts": int(sum(~missing)),
             "n_ineligible": len(ineligible), "ineligible_abstentions": sum(by_id[r["id"]]["status"] == "abstain" for r in ineligible),
             "statuses_all": dict(Counter(by_id[r["id"]]["status"] for r in all_items)),
             "families": sorted(set(families.tolist())), "all_eligible_metrics": {n: metrics(y, v) for n, v in pred.items()},
             "common_valid_subset_metrics": {n: metrics(y[~missing], v[~missing]) for n, v in pred.items()},
             "fallback_policy": "Eligible failed/missing/abstained forecast receives p=0.5 for raw and fitted pipelines; constant always available.",
             "missing_raw_loss_bounds": {"brier": [float(np.sum(losses(y[~missing], p[~missing])[0]) / len(y)), float((np.sum(losses(y[~missing], p[~missing])[0]) + sum(missing)) / len(y))],
                                         "log_loss": [float(np.sum(losses(y[~missing], p[~missing])[1]) / len(y)), float((np.sum(losses(y[~missing], p[~missing])[1]) - sum(missing) * math.log(EPS)) / len(y))]}}
        if split == "test":
            s["uncertainty"] = bootstrap(y, pred, families)
        report["splits"][split] = s
        for i, row in enumerate(selected):
            table.append({"id": row["id"], "family": row["family"], "split": split, "label": int(y[i]),
                          "status": by_id[row["id"]]["status"], "fallback_used": bool(missing[i]),
                          "probabilities": {n: float(v[i]) for n, v in pred.items()}})
    target = ROOT / "results/analysis.json" if output is None else output
    if target.exists():
        assert read_json(target) == report, "Existing analysis differs; do not overwrite empirical evidence"
    else:
        atomic_json(target, report)
    if output is None:
        atomic_json(ROOT / "results/scored_rows.json", table)
    print("Reproducible analysis: " + sha(target.read_bytes()))


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("action", choices=["select", "evaluate"])
    p.add_argument("--output", type=lambda s: __import__("pathlib").Path(s))
    args = p.parse_args()
    select() if args.action == "select" else evaluate(args.output)
