#!/usr/bin/env python3
"""Evaluate theorem coverage judges on the 5-metric panel (RPS, CE, TVD, Pearson, Spearman) plus agreement diagnostics.

TLDR: Computes normalized Ranked Probability Score (RPS, primary), Cross-Entropy (CE, secondary),
Total Variation Distance (TVD, secondary), Pearson r, Spearman rho, Kendall tau-b, nRMSE, MAE,
signed bias, ICC(A,1)/ICC(C,1), and exact Pearson MSE decompositions across splits and judge pools,
using CPU-only cached judge receipts ($0 API calls) or Experiment-09 rating CSVs + forecast JSONs.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
import math
import platform
import sys
import time
from pathlib import Path

import numpy as np
import scipy
from scipy import stats

ROOT = Path(__file__).resolve().parents[3]
EXP_DIR = Path(__file__).resolve().parents[1]
EXP21_SCRIPTS = ROOT / "experiments/21_add_3_frontier_judges_to_pool_pearson_vs_ce_80_20_start_16Nov2026/scripts"
sys.path.insert(0, str(EXP21_SCRIPTS / "exp10_scripts"))
sys.path.insert(0, str(EXP21_SCRIPTS / "vendor_exp03"))

from ce_mixture import fit as fit_ce_or_pearson  # noqa: E402
from models import histogram, smooth  # noqa: E402

GRID = np.arange(6, dtype=float) / 5.0
EPS_PRIMARY = 1e-6
EPS_ALT = 1e-3
LAPLACE_ALPHA = 0.5
SHRINKAGE_GRID = (0.0, 0.05, 0.10, 0.25, 0.50, 1.0)
TIE_TOL = 1e-12
CERT_TOL = 1e-8
BOOT_SEED_EXP100 = 20260928

DEFAULT_DATASET_JSON = Path(
    "/Users/brandomiranda/judges-dont-need-psychometrics-or-corr/experiments/"
    "02_exp06_ce_vs_pearson_matched_budget_start_09Nov2026/private/historical_exp06/cached_v1/dataset.json"
)
DEFAULT_EXP100_RECEIPT = (
    ROOT
    / "experiments/archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026/exp100_TEST_RECEIPT.json"
)
DEFAULT_EXP100_POSTHOC = (
    ROOT
    / "experiments/archive/01_veribench_25_tasks_3_samples_5_raters_judge_evaluation_start_03May2026_end_29Sep2026/POSTHOC_ERROR_INTERVALS_11-06-2026.json"
)
DEFAULT_EXP21_RESULTS = ROOT / "experiments/21_add_3_frontier_judges_to_pool_pearson_vs_ce_80_20_start_16Nov2026/results"
DEFAULT_EXP10_RESULTS = (
    ROOT
    / "experiments/archive/10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability_start_09Nov2026_end_09Nov2026/results/results.json"
)
DEFAULT_OUT = EXP_DIR / "results/aggregates_5metrics.json"

FORBIDDEN_PRIVATE_KEYS = frozenset(
    {"ratings", "ratings_by_expert", "outputs", "raw_scores", "p1", "p2", "p3", "p4", "p5", "per_item", "per_artifact"}
)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def laplace_smooth(counts: np.ndarray, alpha: float = LAPLACE_ALPHA) -> np.ndarray:
    """Laplace/Dirichlet smoothing (count + alpha) / (K + 6*alpha)."""
    counts = np.asarray(counts, dtype=float)
    q = counts + alpha
    return q / q.sum(axis=-1, keepdims=True)


def counts_from_ratings(rating_lists: list[list[int]]) -> np.ndarray:
    out = np.zeros((len(rating_lists), 6), dtype=float)
    for idx, vals in enumerate(rating_lists):
        if len(vals) == 0:
            raise ValueError(f"Empty rating vector at index {idx}")
        for v in vals:
            iv = int(v)
            if iv < 0 or iv > 5 or iv != v:
                raise ValueError(f"Rating must be integer 0..5, got {v!r}")
            out[idx, iv] += 1.0
    return out


def rps_components(P: np.ndarray, Q: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return (rps, empirical_cdf_sq_dist, empirical_disagreement) per artifact."""
    pc = np.cumsum(P, axis=-1)[..., :5]
    qc = np.cumsum(Q, axis=-1)[..., :5]
    cdf_sq = np.mean((qc - pc) ** 2, axis=-1)
    disagree = np.mean(pc * (1.0 - pc), axis=-1)
    rps_arr = np.mean((qc - pc) ** 2 + pc * (1.0 - pc), axis=-1)
    if not np.allclose(rps_arr, cdf_sq + disagree, rtol=0.0, atol=1e-13):
        raise AssertionError("RPS decomposition identity failed beyond 1e-13")
    return rps_arr, cdf_sq, disagree


def ce_per_artifact(P: np.ndarray, Q: np.ndarray) -> np.ndarray:
    """Cross-entropy -sum_r P_r ln(Q_r) per artifact (0 * log(0) = 0; positive P with Q=0 -> inf)."""
    out = np.zeros(len(P), dtype=float)
    for i in range(len(P)):
        mask = P[i] > 0.0
        if np.any(Q[i, mask] <= 0.0):
            out[i] = float("inf")
        else:
            out[i] = float(-np.sum(P[i, mask] * np.log(Q[i, mask])))
    return out


def tvd_per_artifact(P: np.ndarray, Q: np.ndarray) -> np.ndarray:
    return 0.5 * np.sum(np.abs(Q - P), axis=-1)


def brier_per_artifact(P: np.ndarray, Q: np.ndarray) -> np.ndarray:
    """Six-category Brier score averaged over each artifact's observed ratings: sum_s q_s^2 - 2 sum_s p_s q_s + 1."""
    return np.sum(Q ** 2, axis=-1) - 2.0 * np.sum(P * Q, axis=-1) + 1.0


def icc_a1_c1(judge: np.ndarray, human: np.ndarray) -> tuple[float, float]:
    """Two-way random/mixed single-score ICC(A,1) and ICC(C,1) (McGraw & Wong 1996)."""
    n = len(judge)
    if n < 2 or np.ptp(judge) == 0 or np.ptp(human) == 0:
        return float("nan"), float("nan")
    y = np.column_stack([judge, human])
    k = 2
    grand = y.mean()
    ss_rows = k * ((y.mean(axis=1) - grand) ** 2).sum()
    ss_cols = n * ((y.mean(axis=0) - grand) ** 2).sum()
    ss_error = ((y - grand) ** 2).sum() - ss_rows - ss_cols
    ms_rows = ss_rows / (n - 1)
    ms_cols = ss_cols / (k - 1)
    ms_error = ss_error / ((n - 1) * (k - 1))
    denom_c = ms_rows + (k - 1) * ms_error
    denom_a = denom_c + k * (ms_cols - ms_error) / n
    icc_c = (ms_rows - ms_error) / denom_c if abs(denom_c) > 1e-15 else float("nan")
    icc_a = (ms_rows - ms_error) / denom_a if abs(denom_a) > 1e-15 else float("nan")
    return float(icc_a), float(icc_c)


def safe_correlations(x: np.ndarray, y: np.ndarray) -> dict[str, float]:
    if len(x) < 2 or np.ptp(x) <= 1e-12 or np.ptp(y) <= 1e-12:
        return {"pearson": float("nan"), "spearman": float("nan"), "kendall_tau_b": float("nan")}
    return {
        "pearson": float(stats.pearsonr(x, y)[0]),
        "spearman": float(stats.spearmanr(x, y)[0]),
        "kendall_tau_b": float(stats.kendalltau(x, y)[0]),
    }


def mse_decomposition(x: np.ndarray, y: np.ndarray) -> dict[str, float]:
    """Exact decomposition: MSE(x,y) = (x_bar - y_bar)^2 + (s_x - s_y)^2 + 2 s_x s_y (1 - r)."""
    diff = x - y
    mse = float(np.mean(diff ** 2))
    bias_sq = float((x.mean() - y.mean()) ** 2)
    sx = float(np.sqrt(np.mean((x - x.mean()) ** 2)))
    sy = float(np.sqrt(np.mean((y - y.mean()) ** 2)))
    scale_sq = float((sx - sy) ** 2)
    r = float(stats.pearsonr(x, y)[0]) if sx > 1e-12 and sy > 1e-12 else float("nan")
    corr_term = float(2.0 * sx * sy * (1.0 - r)) if np.isfinite(r) else float("nan")
    if np.isfinite(corr_term):
        err = abs(mse - (bias_sq + scale_sq + corr_term))
        if err > 1e-12:
            raise AssertionError(f"MSE decomposition mismatch: {err}")
    return {
        "mse_0_1": mse,
        "bias_sq_0_1": bias_sq,
        "scale_mismatch_sq_0_1": scale_sq,
        "ordering_imperfection_0_1": corr_term,
        "bias_share_of_mse": float(bias_sq / mse) if mse > 1e-15 else float("nan"),
        "scale_share_of_mse": float(scale_sq / mse) if mse > 1e-15 else float("nan"),
        "ordering_share_of_mse": float(corr_term / mse) if (mse > 1e-15 and np.isfinite(corr_term)) else float("nan"),
        "judge_sd_0_1": sx,
        "human_sd_0_1": sy,
    }


def _clean_float(val: float) -> float | str | None:
    if isinstance(val, float) and math.isinf(val):
        return "Infinity"
    if isinstance(val, float) and math.isnan(val):
        return None
    return float(val)


def _clean_dict(obj):
    if isinstance(obj, (bool, np.bool_)):
        return bool(obj)
    if isinstance(obj, dict):
        return {k: _clean_dict(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_clean_dict(v) for v in obj]
    if isinstance(obj, (np.floating, float)):
        return _clean_float(float(obj))
    if isinstance(obj, (np.integer, int)):
        return int(obj)
    return obj


def compute_panel(
    P: np.ndarray,
    Q: np.ndarray,
    scalar_pred: np.ndarray | None = None,
) -> dict[str, object]:
    """Compute the full 5-metric panel + Hard Rule 11 diagnostics for equal-weighted artifacts."""
    P = np.asarray(P, dtype=float)
    Q = np.asarray(Q, dtype=float)
    mu = (Q @ GRID) if scalar_pred is None else np.asarray(scalar_pred, dtype=float)
    hm = P @ GRID

    rps_arr, cdf_sq_arr, disagree_arr = rps_components(P, Q)
    ce_arr = ce_per_artifact(P, Q)
    tvd_arr = tvd_per_artifact(P, Q)
    brier_arr = brier_per_artifact(P, Q)
    corrs = safe_correlations(mu, hm)
    icc_a, icc_c = icc_a1_c1(mu, hm)
    err = mu - hm
    decomp = mse_decomposition(mu, hm)

    n = len(P)
    return {
        "n_artifacts": int(n),
        # 5 core metrics
        "rps": float(np.mean(rps_arr)),
        "ce": float(np.mean(ce_arr)),
        "tvd": float(np.mean(tvd_arr)),
        "pearson": corrs["pearson"],
        "spearman": corrs["spearman"],
        # Hard Rule 11 + secondary distribution diagnostics
        "kendall_tau_b": corrs["kendall_tau_b"],
        "empirical_cdf_sq_dist": float(np.mean(cdf_sq_arr)),
        "empirical_disagreement": float(np.mean(disagree_arr)),
        "root_mean_cdf_distance": float(np.sqrt(np.mean(cdf_sq_arr))),
        "brier_6cat": float(np.mean(brier_arr)),
        "nrmse_0_1": float(np.sqrt(np.mean(err ** 2))),
        "mae_0_1": float(np.mean(np.abs(err))),
        "signed_bias_0_1": float(np.mean(err)),
        "judge_mean_0_1": float(np.mean(mu)),
        "human_mean_0_1": float(np.mean(hm)),
        "mae_0_5": float(5.0 * np.mean(np.abs(err))),
        "signed_bias_0_5": float(5.0 * np.mean(err)),
        "judge_mean_0_5": float(5.0 * np.mean(mu)),
        "human_mean_0_5": float(5.0 * np.mean(hm)),
        "icc_A1": icc_a,
        "icc_C1": icc_c,
        "mse_decomposition": decomp,
    }


def task_bootstrap_panel(
    P: np.ndarray,
    Q: np.ndarray,
    tasks: np.ndarray,
    scalar_pred: np.ndarray | None = None,
    baseline_Q: np.ndarray | None = None,
    baseline_scalar: np.ndarray | None = None,
    draws: int = 10000,
    seed: int = BOOT_SEED_EXP100,
) -> dict[str, object]:
    """Whole-task cluster bootstrap preserving all artifacts within each resampled task."""
    P = np.asarray(P, dtype=float)
    Q = np.asarray(Q, dtype=float)
    tasks = np.asarray(tasks)
    mu = (Q @ GRID) if scalar_pred is None else np.asarray(scalar_pred, dtype=float)
    hm = P @ GRID

    rps_arr, cdf_sq_arr, _ = rps_components(P, Q)
    ce_arr = ce_per_artifact(P, Q)
    tvd_arr = tvd_per_artifact(P, Q)
    brier_arr = brier_per_artifact(P, Q)
    err = mu - hm

    has_base = baseline_Q is not None
    if has_base:
        bQ = np.asarray(baseline_Q, dtype=float)
        b_mu = (bQ @ GRID) if baseline_scalar is None else np.asarray(baseline_scalar, dtype=float)
        b_rps, b_cdf_sq, _ = rps_components(P, bQ)
        b_ce = ce_per_artifact(P, bQ)
        b_tvd = tvd_per_artifact(P, bQ)
        b_brier = brier_per_artifact(P, bQ)
        b_err = b_mu - hm

    task_ids = sorted(set(tasks.tolist()))
    positions = [np.flatnonzero(tasks == t) for t in task_ids]
    n_tasks = len(task_ids)
    rng = np.random.default_rng(seed)

    keys = [
        "rps",
        "ce",
        "tvd",
        "pearson",
        "spearman",
        "kendall_tau_b",
        "empirical_cdf_sq_dist",
        "root_mean_cdf_distance",
        "brier_6cat",
        "nrmse_0_1",
        "mae_0_1",
        "signed_bias_0_1",
        "icc_A1",
        "icc_C1",
    ]
    samples: dict[str, list[float]] = {k: [] for k in keys}
    paired_keys = ["rps", "ce", "tvd", "brier_6cat", "empirical_cdf_sq_dist", "nrmse_0_1", "mae_0_1", "pearson", "spearman", "kendall_tau_b", "icc_A1"]
    paired: dict[str, list[float]] = {k: [] for k in paired_keys} if has_base else {}

    for _ in range(draws):
        picked = rng.integers(0, n_tasks, size=n_tasks)
        idx = np.concatenate([positions[i] for i in picked])
        samples["rps"].append(float(np.mean(rps_arr[idx])))
        samples["ce"].append(float(np.mean(ce_arr[idx])))
        samples["tvd"].append(float(np.mean(tvd_arr[idx])))
        samples["empirical_cdf_sq_dist"].append(float(np.mean(cdf_sq_arr[idx])))
        samples["root_mean_cdf_distance"].append(float(np.sqrt(np.mean(cdf_sq_arr[idx]))))
        samples["brier_6cat"].append(float(np.mean(brier_arr[idx])))
        samples["nrmse_0_1"].append(float(np.sqrt(np.mean(err[idx] ** 2))))
        samples["mae_0_1"].append(float(np.mean(np.abs(err[idx]))))
        samples["signed_bias_0_1"].append(float(np.mean(err[idx])))
        c = safe_correlations(mu[idx], hm[idx])
        samples["pearson"].append(c["pearson"])
        samples["spearman"].append(c["spearman"])
        samples["kendall_tau_b"].append(c["kendall_tau_b"])
        ia, ic = icc_a1_c1(mu[idx], hm[idx])
        samples["icc_A1"].append(ia)
        samples["icc_C1"].append(ic)

        if has_base:
            paired["rps"].append(float(np.mean(rps_arr[idx] - b_rps[idx])))
            paired["ce"].append(float(np.mean(ce_arr[idx] - b_ce[idx])))
            paired["tvd"].append(float(np.mean(tvd_arr[idx] - b_tvd[idx])))
            paired["brier_6cat"].append(float(np.mean(brier_arr[idx] - b_brier[idx])))
            paired["empirical_cdf_sq_dist"].append(float(np.mean(cdf_sq_arr[idx] - b_cdf_sq[idx])))
            paired["nrmse_0_1"].append(float(np.sqrt(np.mean(err[idx] ** 2)) - np.sqrt(np.mean(b_err[idx] ** 2))))
            paired["mae_0_1"].append(float(np.mean(np.abs(err[idx])) - np.mean(np.abs(b_err[idx]))))
            bc = safe_correlations(b_mu[idx], hm[idx])
            bia, _ = icc_a1_c1(b_mu[idx], hm[idx])
            paired["pearson"].append(c["pearson"] - bc["pearson"] if np.isfinite(c["pearson"]) and np.isfinite(bc["pearson"]) else float("nan"))
            paired["spearman"].append(c["spearman"] - bc["spearman"] if np.isfinite(c["spearman"]) and np.isfinite(bc["spearman"]) else float("nan"))
            paired["kendall_tau_b"].append(c["kendall_tau_b"] - bc["kendall_tau_b"] if np.isfinite(c["kendall_tau_b"]) and np.isfinite(bc["kendall_tau_b"]) else float("nan"))
            paired["icc_A1"].append(ia - bia if np.isfinite(ia) and np.isfinite(bia) else float("nan"))

    point = compute_panel(P, Q, scalar_pred=scalar_pred)
    intervals = {}
    for k, vals in samples.items():
        arr = np.asarray(vals, dtype=float)
        finite = arr[np.isfinite(arr)]
        if len(finite) == 0:
            intervals[k] = {"point": point[k], "lo95": None, "hi95": None, "valid_draws": 0, "sd": None}
        else:
            lo, hi = np.percentile(finite, [2.5, 97.5])
            intervals[k] = {
                "point": point[k],
                "lo95": float(lo),
                "hi95": float(hi),
                "valid_draws": int(len(finite)),
                "sd": float(np.std(finite, ddof=1)) if len(finite) > 1 else 0.0,
            }

    out: dict[str, object] = {
        "n_tasks": int(n_tasks),
        "n_artifacts": int(len(P)),
        "draws_requested": int(draws),
        "seed": int(seed),
        "resampling_unit": "task_cluster_with_replacement",
        "point": point,
        "intervals_95": intervals,
    }
    if has_base:
        base_pt = compute_panel(P, bQ, scalar_pred=baseline_scalar)
        paired_out = {}
        for k, vals in paired.items():
            arr = np.asarray(vals, dtype=float)
            finite = arr[np.isfinite(arr)]
            pt_diff = (
                float(point[k] - base_pt[k])
                if (isinstance(point[k], float) and isinstance(base_pt[k], float) and np.isfinite(point[k]) and np.isfinite(base_pt[k]))
                else float("nan")
            )
            if len(finite) == 0:
                paired_out[k] = {
                    "point_diff": pt_diff,
                    "lo95": None,
                    "hi95": None,
                    "excludes_zero": False,
                    "p_val_two_sided": None,
                    "p_test": "paired_task_bootstrap_zero_diff",
                    "valid_draws": 0,
                }
            else:
                lo, hi = np.percentile(finite, [2.5, 97.5])
                p_two = float(min(1.0, max(1.0 / len(finite), 2.0 * min(np.mean(finite <= 0.0), np.mean(finite >= 0.0)))))
                paired_out[k] = {
                    "point_diff": pt_diff,
                    "lo95": float(lo),
                    "hi95": float(hi),
                    "excludes_zero": bool(lo > 0.0 or hi < 0.0),
                    "p_val_two_sided": p_two,
                    "p_test": "paired_task_bootstrap_zero_diff",
                    "valid_draws": int(len(finite)),
                }
        out["paired_minus_baseline"] = paired_out
    return out


def fit_rps_simplex(q: np.ndarray, p: np.ndarray, certificate_tol: float = CERT_TOL, tie_tol: float = TIE_TOL) -> tuple[np.ndarray, dict[str, object]]:
    """Globally optimal simplex mixture minimizing RPS (convex quadratic over 1<=m<=8 candidates)."""
    q = np.asarray(q, dtype=float)
    p = np.asarray(p, dtype=float)
    n, m, k = q.shape
    assert k == 6 and p.shape == (n, 6) and n >= 2 and 1 <= m <= 8
    design = np.cumsum(q, axis=2)[:, :, :5].transpose(0, 2, 1).reshape(-1, m) / np.sqrt(5.0 * n)
    target = np.cumsum(p, axis=1)[:, :5].ravel() / np.sqrt(5.0 * n)
    gram, rhs = design.T @ design, design.T @ target
    candidates, rejected, solved = [], 0, 0
    for size in range(1, m + 1):
        for face in itertools.combinations(range(m), size):
            solved += 1
            ix = np.array(face)
            system = np.block(
                [[gram[np.ix_(ix, ix)], np.ones((size, 1))], [np.ones((1, size)), np.zeros((1, 1))]]
            )
            b = np.r_[rhs[ix], 1.0]
            answer = np.linalg.lstsq(system, b, rcond=None)[0]
            if np.linalg.norm(system @ answer - b) > 1e-10 * (1.0 + np.linalg.norm(b)) or answer[:-1].min() < -1e-10:
                rejected += 1
                continue
            w = np.zeros(m)
            w[ix] = np.maximum(answer[:-1], 0.0)
            w /= w.sum()
            candidates.append((float(np.sum((design @ w - target) ** 2)), w, face))
    if not candidates:
        raise ArithmeticError("No feasible RPS face found.")
    best = min(a[0] for a in candidates)
    tied = [a for a in candidates if a[0] <= best + tie_tol * (1.0 + abs(best))]

    def tie_key(a):
        support = tuple(np.flatnonzero(a[1] > 1e-10).tolist())
        return len(support), support, len(a[2]), a[2]

    value, weights, face = min(tied, key=tie_key)
    grad = 2.0 * design.T @ (design @ weights - target)
    gap = float(grad @ weights - grad.min())
    pred_mix = np.einsum("njr,j->nr", q, weights)
    train_rps = float(rps_components(p, pred_mix)[0].mean())
    return weights, {
        "objective": "rps",
        "algorithm": "finite_simplex_face_quadratic_v1",
        "success": bool(gap <= certificate_tol),
        "status": "optimal" if gap <= certificate_tol else "certificate_failed",
        "simplex_frank_wolfe_gap": gap,
        "empirical_cdf_squared_distance": value,
        "training_rps": train_rps,
        "faces_total": 2 ** m - 1,
        "linear_solves": solved,
        "feasible_faces": len(candidates),
        "rejected_faces": rejected,
        "selected_face": list(face),
    }


def fit_and_select_pool(
    q_all: np.ndarray,
    p_all: np.ndarray,
    tr_idx: np.ndarray,
    va_idx: np.ndarray,
    candidate_names: list[str],
    shrinkage_grid: tuple[float, ...] = SHRINKAGE_GRID,
) -> dict[str, dict[str, object]]:
    """Fit baselines plus raw (lambda=0) and validation-RPS-selected shrinkage mixtures for methods 2 and 4."""
    q_tr, p_tr = q_all[tr_idx], p_all[tr_idx]
    q_va, p_va = q_all[va_idx], p_all[va_idx]
    m = q_all.shape[1]
    const = smooth(p_tr.mean(axis=0), EPS_PRIMARY)

    models: dict[str, dict[str, object]] = {}
    q_const_all = np.broadcast_to(const, (len(q_all), 6)).copy()
    models["constant_train_marginal"] = {
        "kind": "constant",
        "weights": None,
        "shrinkage": 1.0,
        "Q_all": q_const_all,
        "meta": {"selection": "train_marginal_histogram"},
    }
    w_eq = np.full(m, 1.0 / m)
    models["equal_mixture"] = {
        "kind": "mixture",
        "weights": dict(zip(candidate_names, w_eq.tolist())),
        "shrinkage": 0.0,
        "Q_all": np.einsum("njr,j->nr", q_all, w_eq),
        "meta": {"selection": "uniform_weights"},
    }

    for method_key, loss_type in [
        ("method2_pearson", "pearson"),
        ("method4_ce", "ce"),
        ("method4_rps", "rps"),
    ]:
        candidates = []
        for gi, lam in enumerate(shrinkage_grid):
            qt_shrunk = (1.0 - lam) * q_tr + lam * const
            if lam == 1.0:
                w = w_eq.copy()
                rec = {"status": "shared_constant_baseline", "success": True}
            elif loss_type == "rps":
                w, rec = fit_rps_simplex(qt_shrunk, p_tr)
            else:
                w, rec = fit_ce_or_pearson(qt_shrunk, p_tr, loss_type)
            assert rec.get("success", False), f"{method_key} shrinkage={lam} failed certificate: {rec}"
            q_shrunk_all = (1.0 - lam) * np.einsum("njr,j->nr", q_all, w) + lam * const
            val_rps = float(rps_components(p_va, q_shrunk_all[va_idx])[0].mean())
            candidates.append(
                {
                    "grid_index": gi,
                    "shrinkage": float(lam),
                    "weights": w,
                    "val_rps": val_rps,
                    "Q_all": q_shrunk_all,
                    "rec": rec,
                }
            )
        raw_entry = candidates[0]
        assert raw_entry["shrinkage"] == 0.0
        models[f"{method_key}_raw"] = {
            "kind": "mixture",
            "weights": dict(zip(candidate_names, raw_entry["weights"].tolist())),
            "shrinkage": 0.0,
            "Q_all": raw_entry["Q_all"],
            "meta": {
                "objective": loss_type,
                "status": raw_entry["rec"]["status"],
                "val_rps": raw_entry["val_rps"],
            },
        }
        best_val = min(c["val_rps"] for c in candidates)
        chosen = next(c for c in candidates if c["val_rps"] <= best_val + TIE_TOL)
        models[f"{method_key}_val_rps_shrink"] = {
            "kind": "mixture",
            "weights": dict(zip(candidate_names, chosen["weights"].tolist())),
            "shrinkage": chosen["shrinkage"],
            "Q_all": chosen["Q_all"],
            "meta": {
                "objective": loss_type,
                "status": chosen["rec"]["status"],
                "val_rps": chosen["val_rps"],
                "shrinkage_grid": [{"lambda": c["shrinkage"], "val_rps": c["val_rps"]} for c in candidates],
            },
        }
    return models


def assert_no_private_ratings(obj, path: str = "root") -> None:
    """Programmatic guard preventing raw human ratings or per-item arrays from entering public JSON."""
    if isinstance(obj, dict):
        for k, v in obj.items():
            if k in FORBIDDEN_PRIVATE_KEYS:
                raise AssertionError(f"Forbidden private key {k!r} found at {path}.{k}")
            assert_no_private_ratings(v, f"{path}.{k}")
    elif isinstance(obj, list):
        if len(obj) >= 20 and all(isinstance(x, (int, float)) for x in obj):
            raise AssertionError(f"Suspicious numeric array of length {len(obj)} at {path}")
        for idx, v in enumerate(obj):
            assert_no_private_ratings(v, f"{path}[{idx}]")


def load_veribench_cached(dataset_path: Path, exp21_csv_path: Path) -> dict[str, object]:
    d = json.loads(dataset_path.read_text())
    rows = d["rows"]
    assert len(rows) == 75
    rating_lists = [r["ratings"] for r in rows]
    counts = counts_from_ratings(rating_lists)
    P = counts / counts.sum(axis=1, keepdims=True)
    splits = np.array([r["split"] for r in rows])
    tasks = np.array([r["task"] for r in rows])
    ordinary = np.array([bool(r["ordinary"]) for r in rows])

    old5_names = ["H0_sol", "H0_opus", "H1_sol", "H2_sol", "H2_opus"]
    new3_names = ["H2_astra", "H2_sol61", "H2_argon"]

    csv_lookup: dict[str, dict[str, dict[int, int]]] = {j: {} for j in new3_names}
    with exp21_csv_path.open() as fh:
        for rec in csv.DictReader(fh):
            j = rec["judge"]
            if j in csv_lookup:
                assert rec["status"] == "COMPLETE"
                csv_lookup[j].setdefault(rec["item"], {})[int(rec["repeat"])] = int(rec["score_0to5"])

    judge_calls: dict[str, list[list[int]]] = {}
    for j in old5_names:
        judge_calls[j] = [list(map(int, x)) for x in d["outputs"][j]]
    for j in new3_names:
        judge_calls[j] = [[csv_lookup[j][r["item"]][k] for k in (1, 2, 3)] for r in rows]

    # Exp 100 selected judge: 3 calls H2_sol + 3 calls H2_opus
    exp100_6calls = [judge_calls["H2_sol"][i] + judge_calls["H2_opus"][i] for i in range(75)]
    exp100_med_scalar = np.array(
        [0.5 * (np.median(judge_calls["H2_sol"][i]) + np.median(judge_calls["H2_opus"][i])) / 5.0 for i in range(75)]
    )

    return {
        "source_commit": d.get("source_commit"),
        "rows": rows,
        "P": P,
        "rating_counts": counts,
        "splits": splits,
        "tasks": tasks,
        "ordinary": ordinary,
        "old5_names": old5_names,
        "new3_names": new3_names,
        "all8_names": old5_names + new3_names,
        "judge_calls": judge_calls,
        "exp100_6calls": exp100_6calls,
        "exp100_med_scalar": exp100_med_scalar,
    }


def verify_exp100_receipt(data: dict[str, object], receipt_path: Path, posthoc_path: Path) -> dict[str, object]:
    receipt = json.loads(receipt_path.read_text())
    posthoc = json.loads(posthoc_path.read_text())
    P = data["P"]
    splits = data["splits"]
    ordinary = data["ordinary"]
    med = data["exp100_med_scalar"]
    hm = P @ GRID

    checks = {}
    for name, mask, expected_r, expected_p in [
        ("all_items", splits == "test", receipt["all_items"], posthoc["subsets"]["all_items"]),
        ("ordinary_items", (splits == "test") & ordinary, receipt["ordinary_items"], posthoc["subsets"]["ordinary_items"]),
    ]:
        x, y = med[mask], hm[mask]
        corrs = safe_correlations(x, y)
        icc_a, icc_c = icc_a1_c1(x, y)
        mae = float(np.mean(np.abs(x - y)))
        bias = float(np.mean(x - y))
        diffs = {
            "spearman": abs(corrs["spearman"] - expected_r["spearman"]),
            "kendall_tau_b": abs(corrs["kendall_tau_b"] - expected_r["kendall_tau_b"]),
            "pearson": abs(corrs["pearson"] - expected_r["pearson"]),
            "icc_A1": abs(icc_a - expected_r["icc_A1"]),
            "icc_C1": abs(icc_c - expected_r["icc_C1"]),
            "mae": abs(mae - expected_r["mae"]),
            "mean_pred": abs(float(x.mean()) - expected_r["mean_pred"]),
            "mean_target": abs(float(y.mean()) - expected_r["mean_target"]),
            "mean_bias": abs(bias - expected_p["metrics"]["mean_bias"]["value"]),
        }
        max_diff = max(diffs.values())
        if max_diff >= 1e-12:
            raise AssertionError(f"Exp 100 receipt reproduction failed on {name}: {diffs}")
        checks[name] = {"max_abs_diff": max_diff, "n_items": int(mask.sum()), "verified": True}
    return checks


def run_veribench_eval(args: argparse.Namespace) -> dict[str, object]:
    t0 = time.monotonic()
    data = load_veribench_cached(args.dataset, args.exp21_results / "judge_scores.csv")
    receipt_checks = verify_exp100_receipt(data, args.exp100_receipt, args.exp100_posthoc)

    P = data["P"]
    splits = data["splits"]
    tasks = data["tasks"]
    ordinary = data["ordinary"]
    rating_counts = data["rating_counts"]

    tr_idx = np.flatnonzero(splits == "train")
    va_idx = np.flatnonzero(splits == "val")
    te_idx = np.flatnonzero(splits == "test")
    to_idx = np.flatnonzero((splits == "test") & ordinary)
    all_idx = np.arange(len(P))

    split_defs = [
        ("train", tr_idx, 10000),
        ("val", va_idx, 10000),
        ("test", te_idx, 10000),
        ("test_ordinary", to_idx, 2000),
        ("all_75", all_idx, 10000),
    ]

    # Build train marginal baseline
    const_pmf = smooth(P[tr_idx].mean(axis=0), EPS_PRIMARY)
    Q_const = np.broadcast_to(const_pmf, (len(P), 6)).copy()

    # Build Panel A: Exp 100 selected judge ("0.6, 0.8, 0.8")
    exp100_call_counts = counts_from_ratings(data["exp100_6calls"])
    exp100_probs_1e6 = smooth(exp100_call_counts / 6.0, EPS_PRIMARY)
    exp100_probs_1e3 = smooth(exp100_call_counts / 6.0, EPS_ALT)
    exp100_probs_laplace = laplace_smooth(exp100_call_counts, LAPLACE_ALPHA)

    panel_a = {"splits": {}, "floor_sensitivity": {}, "test_ordinary_10k_check": {}}
    for sp_name, idx, draws in split_defs:
        sp_tasks = tasks[idx]
        med_res = task_bootstrap_panel(
            P[idx],
            exp100_probs_1e6[idx],
            sp_tasks,
            scalar_pred=data["exp100_med_scalar"][idx],
            baseline_Q=Q_const[idx],
            draws=draws,
            seed=BOOT_SEED_EXP100,
        )
        mean6_res = task_bootstrap_panel(
            P[idx],
            exp100_probs_1e6[idx],
            sp_tasks,
            scalar_pred=None,
            baseline_Q=Q_const[idx],
            draws=draws,
            seed=BOOT_SEED_EXP100,
        )
        const_res = task_bootstrap_panel(
            P[idx],
            Q_const[idx],
            sp_tasks,
            scalar_pred=None,
            draws=draws,
            seed=BOOT_SEED_EXP100,
        )
        panel_a["splits"][sp_name] = {
            "n_artifacts": int(len(idx)),
            "n_tasks": int(len(set(sp_tasks.tolist()))),
            "n_ratings": int(rating_counts[idx].sum()),
            "exp100_selected_member_median_scalar": med_res,
            "exp100_selected_pmf_mean_scalar": mean6_res,
            "constant_train_marginal": const_res,
        }
        panel_a["floor_sensitivity"][sp_name] = {
            "eps_1e-6": {
                "rps": float(rps_components(P[idx], exp100_probs_1e6[idx])[0].mean()),
                "ce": float(ce_per_artifact(P[idx], exp100_probs_1e6[idx]).mean()),
                "tvd": float(tvd_per_artifact(P[idx], exp100_probs_1e6[idx]).mean()),
            },
            "eps_1e-3": {
                "rps": float(rps_components(P[idx], exp100_probs_1e3[idx])[0].mean()),
                "ce": float(ce_per_artifact(P[idx], exp100_probs_1e3[idx]).mean()),
                "tvd": float(tvd_per_artifact(P[idx], exp100_probs_1e3[idx]).mean()),
            },
            "laplace_alpha_0.5": {
                "rps": float(rps_components(P[idx], exp100_probs_laplace[idx])[0].mean()),
                "ce": float(ce_per_artifact(P[idx], exp100_probs_laplace[idx]).mean()),
                "tvd": float(tvd_per_artifact(P[idx], exp100_probs_laplace[idx]).mean()),
            },
            "constant_train_marginal_eps_1e-6": {
                "rps": float(rps_components(P[idx], Q_const[idx])[0].mean()),
                "ce": float(ce_per_artifact(P[idx], Q_const[idx]).mean()),
                "tvd": float(tvd_per_artifact(P[idx], Q_const[idx]).mean()),
            },
        }
    panel_a["test_ordinary_10k_check"] = task_bootstrap_panel(
        P[to_idx],
        exp100_probs_1e6[to_idx],
        tasks[to_idx],
        scalar_pred=data["exp100_med_scalar"][to_idx],
        baseline_Q=Q_const[to_idx],
        draws=10000,
        seed=BOOT_SEED_EXP100,
    )

    # Panel B: All 8 single judges + 5-pool and 8-pool mixtures on canonical 10/5/10 split
    all8_names = data["all8_names"]
    old5_names = data["old5_names"]
    q_single = {}
    q_single_floor_sens = {}
    for j in all8_names:
        c = counts_from_ratings(data["judge_calls"][j])
        q_single[j] = smooth(c / 3.0, EPS_PRIMARY)
        q_e3 = smooth(c / 3.0, EPS_ALT)
        q_lap = laplace_smooth(c, LAPLACE_ALPHA)
        q_single_floor_sens[j] = {
            "test_eps_1e-6": {
                "rps": float(rps_components(P[te_idx], q_single[j][te_idx])[0].mean()),
                "ce": float(ce_per_artifact(P[te_idx], q_single[j][te_idx]).mean()),
                "tvd": float(tvd_per_artifact(P[te_idx], q_single[j][te_idx]).mean()),
            },
            "test_eps_1e-3": {
                "rps": float(rps_components(P[te_idx], q_e3[te_idx])[0].mean()),
                "ce": float(ce_per_artifact(P[te_idx], q_e3[te_idx]).mean()),
                "tvd": float(tvd_per_artifact(P[te_idx], q_e3[te_idx]).mean()),
            },
            "test_laplace_0.5": {
                "rps": float(rps_components(P[te_idx], q_lap[te_idx])[0].mean()),
                "ce": float(ce_per_artifact(P[te_idx], q_lap[te_idx]).mean()),
                "tvd": float(tvd_per_artifact(P[te_idx], q_lap[te_idx]).mean()),
            },
        }

    single_judges_out = {}
    for j in all8_names:
        Q_j = q_single[j]
        single_judges_out[j] = {
            "train": compute_panel(P[tr_idx], Q_j[tr_idx]),
            "val": compute_panel(P[va_idx], Q_j[va_idx]),
            "test": task_bootstrap_panel(
                P[te_idx], Q_j[te_idx], tasks[te_idx], baseline_Q=Q_const[te_idx], draws=10000, seed=BOOT_SEED_EXP100
            ),
            "test_ordinary": compute_panel(P[to_idx], Q_j[to_idx]),
            "all_75": compute_panel(P, Q_j),
            "floor_sensitivity": q_single_floor_sens[j],
        }

    q_old5_stack = np.stack([q_single[j] for j in old5_names], axis=1)
    q_all8_stack = np.stack([q_single[j] for j in all8_names], axis=1)

    pool_outputs = {}
    for pool_name, q_stack, names in [
        ("old5", q_old5_stack, old5_names),
        ("all8", q_all8_stack, all8_names),
    ]:
        models = fit_and_select_pool(q_stack, P, tr_idx, va_idx, names)
        eval_models = {}
        for mname, mobj in models.items():
            Q_m = mobj["Q_all"]
            eval_models[mname] = {
                "kind": mobj["kind"],
                "weights": mobj["weights"],
                "shrinkage": mobj["shrinkage"],
                "fit_meta": mobj["meta"],
                "train": compute_panel(P[tr_idx], Q_m[tr_idx]),
                "val": compute_panel(P[va_idx], Q_m[va_idx]),
                "test": task_bootstrap_panel(
                    P[te_idx], Q_m[te_idx], tasks[te_idx], baseline_Q=Q_const[te_idx], draws=10000, seed=BOOT_SEED_EXP100
                ),
                "test_ordinary": compute_panel(P[to_idx], Q_m[to_idx]),
            }
        # Paired method2 minus method4 comparisons on canonical test split
        paired_2_vs_4 = {}
        for variant_suffix in ("raw", "val_rps_shrink"):
            m2 = f"method2_pearson_{variant_suffix}"
            for m4_base in ("method4_ce", "method4_rps"):
                m4 = f"{m4_base}_{variant_suffix}"
                comp = task_bootstrap_panel(
                    P[te_idx],
                    models[m2]["Q_all"][te_idx],
                    tasks[te_idx],
                    baseline_Q=models[m4]["Q_all"][te_idx],
                    draws=10000,
                    seed=BOOT_SEED_EXP100,
                )
                paired_2_vs_4[f"{m2}_minus_{m4}"] = comp["paired_minus_baseline"]
        pool_outputs[pool_name] = {
            "candidate_order": names,
            "models": eval_models,
            "paired_test_method2_minus_method4": paired_2_vs_4,
        }

    # Panel C: Verified 1000-split summaries from Experiment 21 + cross-check with Experiment 10
    r21_old5 = json.loads((args.exp21_results / "results_old5.json").read_text())
    r21_all8 = json.loads((args.exp21_results / "results_all8.json").read_text())
    r10 = json.loads(args.exp10_results.read_text()) if args.exp10_results.is_file() else None

    panel_c = {
        "exp21_old5_1000splits": {
            "splits": r21_old5["splits"],
            "metrics": r21_old5["metrics"],
            "corr_metrics": r21_old5["corr_metrics"],
            "paired": r21_old5["paired"],
        },
        "exp21_all8_1000splits": {
            "splits": r21_all8["splits"],
            "metrics": r21_all8["metrics"],
            "corr_metrics": r21_all8["corr_metrics"],
            "paired": r21_all8["paired"],
        },
        "exp10_canonical_split_check": {
            "rps": {k: v["rps"] for k, v in r10["metrics"]["test"].items()} if r10 else None,
            "ce": {k: v["ce"] for k, v in r10["metrics"]["test"].items()} if r10 else None,
            "tvd": {k: v["tvd"] for k, v in r10["metrics"]["test"].items()} if r10 else None,
        },
    }

    result = _clean_dict(
        {
            "experiment": EXP_DIR.name,
            "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "compute": {
                "mode": "cpu_only_cached_receipts",
                "paid_api_calls": 0,
                "provider_cost_usd": 0.0,
                "dt_applied": False,
                "lean_checked_proofs": False,
                "elapsed_seconds": round(time.monotonic() - t0, 3),
                "python": platform.python_version(),
                "numpy": np.__version__,
                "scipy": scipy.__version__,
            },
            "inputs": {
                "dataset_source_commit": data["source_commit"],
                "dataset_sha256": sha256_file(args.dataset),
                "exp100_receipt_sha256": sha256_file(args.exp100_receipt),
                "exp21_judge_scores_csv_sha256": sha256_file(args.exp21_results / "judge_scores.csv"),
                "exp21_results_old5_sha256": sha256_file(args.exp21_results / "results_old5.json"),
                "exp21_results_all8_sha256": sha256_file(args.exp21_results / "results_all8.json"),
            },
            "exp100_receipt_reproduction_checks": receipt_checks,
            "panel_a_exp100_selected_judge": panel_a,
            "panel_b_canonical_10_5_10": {
                "single_judges": single_judges_out,
                "pools": pool_outputs,
            },
            "panel_c_1000_splits_from_exp21": panel_c,
        }
    )
    assert_no_private_ratings(result)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    return result


def score_forecasts_cli(args: argparse.Namespace) -> dict[str, object]:
    """Reusable evaluator for Experiment-09 rating CSVs + JSON forecast distributions."""
    forecasts_raw = json.loads(args.forecasts_json.read_text())
    if isinstance(forecasts_raw, dict) and "forecasts" in forecasts_raw:
        forecasts_raw = forecasts_raw["forecasts"]

    forecasts: dict[str, np.ndarray] = {}
    for item_id, vec in forecasts_raw.items():
        arr = np.asarray(vec, dtype=float)
        if arr.shape != (6,) or not np.isfinite(arr).all() or arr.min() < 0.0:
            raise ValueError(f"Invalid probability vector for {item_id!r}: {vec!r}")
        if abs(float(arr.sum()) - 1.0) > 1e-6:
            raise ValueError(f"Probability vector for {item_id!r} sums to {arr.sum()}, expected 1.0")
        forecasts[str(item_id)] = arr / arr.sum()

    seen_pairs: dict[tuple[str, str], int] = {}
    item_ratings: dict[str, list[int]] = {}
    item_tasks: dict[str, str] = {}
    unscored_rows = 0

    for csv_path in args.ratings_csv:
        with csv_path.open(newline="") as fh:
            reader = csv.DictReader(fh)
            fieldnames = set(reader.fieldnames or [])
            task_col = args.task_col
            if task_col is None:
                if "task_folder" in fieldnames:
                    task_col = "task_folder"
                elif "task_id" in fieldnames:
                    task_col = "task_id"
                elif "task" in fieldnames:
                    task_col = "task"
                else:
                    raise ValueError(f"No task column found in {csv_path}; specify --task-col")

            for row in reader:
                item_id = row[args.item_col].strip()
                rater_id = row.get("rater_id", row.get("rater_name", "unknown")).strip()
                task_id = row[task_col].strip()
                raw_score = row[args.score_col].strip()
                if item_id in item_tasks and item_tasks[item_id] != task_id:
                    raise ValueError(f"Conflicting task_id for {item_id}: {item_tasks[item_id]} vs {task_id}")
                item_tasks[item_id] = task_id
                if raw_score == "" or raw_score.upper() == "N/A":
                    unscored_rows += 1
                    continue
                val = int(float(raw_score))
                if float(raw_score) != val or val < 0 or val > 5:
                    raise ValueError(f"Score must be integer 0..5 for {item_id} ({rater_id}), got {raw_score!r}")
                pair = (rater_id, item_id)
                if pair in seen_pairs and seen_pairs[pair] != val:
                    raise ValueError(f"Conflicting duplicate rating for {pair}: {seen_pairs[pair]} vs {val}")
                if pair not in seen_pairs:
                    seen_pairs[pair] = val
                    item_ratings.setdefault(item_id, []).append(val)

    rated_items = sorted(item_ratings.keys())
    scored_items = [it for it in rated_items if it in forecasts]
    missing_forecasts = [it for it in rated_items if it not in forecasts]
    if not scored_items:
        raise ValueError("No overlapping rated items found between --ratings-csv and --forecasts-json")

    counts = counts_from_ratings([item_ratings[it] for it in scored_items])
    P = counts / counts.sum(axis=1, keepdims=True)
    Q = np.stack([forecasts[it] for it in scored_items], axis=0)
    tasks = np.array([item_tasks[it] for it in scored_items])

    const_pmf = smooth(P.mean(axis=0), EPS_PRIMARY)
    Q_const = np.broadcast_to(const_pmf, (len(P), 6)).copy()

    res = task_bootstrap_panel(
        P,
        Q,
        tasks,
        baseline_Q=Q_const,
        draws=args.bootstrap,
        seed=args.seed,
    )
    out = _clean_dict(
        {
            "mode": "score_forecasts",
            "n_rated_items": len(rated_items),
            "n_scored_items": len(scored_items),
            "n_missing_forecasts": len(missing_forecasts),
            "n_unscored_csv_rows": unscored_rows,
            "n_ratings_scored": int(counts.sum()),
            "n_tasks_scored": int(len(set(tasks.tolist()))),
            "evaluation": res,
            "in_sample_constant_baseline": compute_panel(P, Q_const),
        }
    )
    assert_no_private_ratings(out)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(out, indent=2) + "\n")
    return out


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd")

    p_vb = sub.add_parser("run-veribench", help="Evaluate cached VeriBench judges and mixtures on the 5-metric panel")
    p_vb.add_argument("--dataset", type=Path, default=DEFAULT_DATASET_JSON)
    p_vb.add_argument("--exp100-receipt", type=Path, default=DEFAULT_EXP100_RECEIPT)
    p_vb.add_argument("--exp100-posthoc", type=Path, default=DEFAULT_EXP100_POSTHOC)
    p_vb.add_argument("--exp21-results", type=Path, default=DEFAULT_EXP21_RESULTS)
    p_vb.add_argument("--exp10-results", type=Path, default=DEFAULT_EXP10_RESULTS)
    p_vb.add_argument("--out", type=Path, default=DEFAULT_OUT)

    p_sf = sub.add_parser("score-forecasts", help="Score Experiment-09 rating CSVs against a JSON map of forecasts")
    p_sf.add_argument("--ratings-csv", type=Path, nargs="+", required=True)
    p_sf.add_argument("--forecasts-json", type=Path, required=True)
    p_sf.add_argument("--item-col", default="item_id")
    p_sf.add_argument("--task-col", default=None)
    p_sf.add_argument("--score-col", default="final_score_0_5")
    p_sf.add_argument("--bootstrap", type=int, default=10000)
    p_sf.add_argument("--seed", type=int, default=20261116)
    p_sf.add_argument("--out", type=Path, default=None)
    return ap


def main(argv: list[str] | None = None) -> None:
    parser = build_parser()
    raw_argv = sys.argv[1:] if argv is None else argv
    if not raw_argv or raw_argv[0].startswith("-"):
        raw_argv = ["run-veribench", *raw_argv]
    args = parser.parse_args(raw_argv)
    if args.cmd == "run-veribench":
        res = run_veribench_eval(args)
        pa = res["panel_a_exp100_selected_judge"]["splits"]
        summary = {
            sp: {
                k: pa[sp]["exp100_selected_member_median_scalar"]["point"][k]
                for k in ("rps", "ce", "tvd", "pearson", "spearman", "mae_0_1", "signed_bias_0_1")
            }
            for sp in ("train", "val", "test", "test_ordinary", "all_75")
        }
        print(json.dumps({"written": str(args.out), "exp100_selected_5metrics": summary}, indent=2))
    elif args.cmd == "score-forecasts":
        out = score_forecasts_cli(args)
        print(json.dumps(out, indent=2))
    else:
        parser.error(f"Unknown command: {args.cmd}")


if __name__ == "__main__":
    main()
