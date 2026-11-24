#!/usr/bin/env python3
"""Quantitative analysis of how Old 25 + New 25 (Exp 09) human ratings resolve '0.6, 0.8, 0.8',
expand 5-metric evaluation (RPS, CE, TVD, Pearson, Spearman), and bridge to cert-judge.

CPU-only ($0.00 API spend, no DT, not Lean-checked proofs). Never reads `sealed/`
item-to-agent mappings and never tunes any model on Experiment 09 ratings.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import re
import statistics
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.stats import rankdata

ROOT = Path(__file__).resolve().parents[3]
EXP26_DIR = Path(__file__).resolve().parents[1]
EXP09_DIR = ROOT / "experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026"
EXP22_DIR = ROOT / "experiments/22_evaluate_veribench_judges_on_75_outputs_distribution_losses_vs_correlations_start_16Nov2026"
CERT_JUDGE_DIR = Path.home() / "cert-judge"
JUDGES_CORR_DIR = Path.home() / "judges-dont-need-psychometrics-or-corr"
DATASET_JSON_PATH = (
    JUDGES_CORR_DIR
    / "experiments/02_exp06_ce_vs_pearson_matched_budget_start_09Nov2026/private/historical_exp06/cached_v1/dataset.json"
)

sys.path.insert(0, str(EXP22_DIR / "scripts"))
import evaluate_5metrics as e5  # noqa: E402

SEED = 20261124
BOOT_DRAWS = 10000
PERM_DRAWS = 10000
EPS_PRIMARY = 1e-6
EPS_ALT = 1e-3
LAPLACE_ALPHA = 0.5
FORBIDDEN_KEYS = frozenset(
    {
        "ratings",
        "ratings_by_expert",
        "outputs",
        "raw_scores",
        "per_item",
        "per_artifact",
        "sealed",
        "agent_map",
    }
)

_THEOREM_ALL_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|unsafe)[ \t]+)*(?:theorem|lemma)\b"
)
_THEOREM_PUBLIC_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:noncomputable|unsafe)[ \t]+)*(?:theorem|lemma)\b"
)


def assert_no_private_leak(obj) -> None:
    """Reject any forbidden raw-rating or sealed key before writing public JSON."""
    if isinstance(obj, dict):
        for k, v in obj.items():
            if k in FORBIDDEN_KEYS:
                raise AssertionError(f"Forbidden private/raw key {k!r} in public aggregate output")
            assert_no_private_leak(v)
    elif isinstance(obj, list):
        for v in obj:
            assert_no_private_leak(v)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_lean_comments_and_strings(src: str) -> str:
    """Replace Lean comments (--, /- ... -/), char literals, and string literals with spaces, preserving newlines."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        if depth == 0 and not in_str and src[i] == '"':
            in_str = True
            out.append(" ")
            i += 1
        elif in_str:
            if src[i] == "\\" and i + 1 < n:
                out.extend((" ", " "))
                i += 2
            elif src[i] == '"':
                in_str = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if src[i] == "\n" else " ")
                i += 1
        elif depth == 0 and src[i] == "'":
            prev_is_ident = i > 0 and (src[i - 1].isalnum() or src[i - 1] in ("_", "'", "!", "?"))
            if not prev_is_ident:
                if i + 2 < n and src[i + 1] != "\\" and src[i + 1] != "\n" and src[i + 2] == "'":
                    out.extend((" ", " ", " "))
                    i += 3
                    continue
                if i + 3 < n and src[i + 1] == "\\":
                    j = i + 2
                    if j < n and src[j] in ("x", "u"):
                        j += 1
                        while j < n and src[j] in "0123456789abcdefABCDEF":
                            j += 1
                    else:
                        j += 1
                    if j < n and src[j] == "'":
                        out.extend([" "] * (j - i + 1))
                        i = j + 1
                        continue
            out.append(src[i])
            i += 1
        elif src[i : i + 2] == "/-":
            depth += 1
            out.extend((" ", " "))
            i += 2
        elif depth > 0 and src[i : i + 2] == "-/":
            depth -= 1
            out.extend((" ", " "))
            i += 2
        elif depth == 0 and src[i : i + 2] == "--":
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
        elif depth == 0:
            out.append(src[i])
            i += 1
        else:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
    return "".join(out)


def count_theorems(lean_text: str, public_only: bool = False) -> int:
    """Count top-level theorem/lemma declarations after masking comments and strings."""
    cleaned = strip_lean_comments_and_strings(lean_text)
    pat = _THEOREM_PUBLIC_RE if public_only else _THEOREM_ALL_RE
    return len(pat.findall(cleaned))


def linear_interp_pmf(score_0_5: float) -> np.ndarray:
    """Map a continuous 0..5 scalar linearly onto adjacent integer categories 0..5."""
    clipped = min(5.0, max(0.0, float(score_0_5)))
    lo, hi = int(math.floor(clipped)), int(math.ceil(clipped))
    q = np.zeros(6, dtype=float)
    if lo == hi:
        q[lo] = 1.0
    else:
        frac = clipped - lo
        q[lo], q[hi] = 1.0 - frac, frac
    return q


def smooth_pmf(q: np.ndarray, eps: float = EPS_PRIMARY) -> np.ndarray:
    arr = np.maximum(np.asarray(q, dtype=float), eps)
    return arr / arr.sum()


def laplace_smooth_counts(count_rows: np.ndarray | list[np.ndarray], alpha: float = LAPLACE_ALPHA) -> np.ndarray:
    """Apply Dirichlet/Laplace smoothing per artifact using each artifact's actual sample/repeat count."""
    return np.vstack(
        [(np.asarray(c, dtype=float) + alpha) / (np.asarray(c, dtype=float).sum() + 6.0 * alpha) for c in count_rows]
    )


def one_hot_pmf(rating: int) -> np.ndarray:
    q = np.zeros(6, dtype=float)
    q[int(rating)] = 1.0
    return q


def _load_old_dataset() -> dict:
    return json.loads(DATASET_JSON_PATH.read_text())


def _clean_float(x: float | None) -> float | None:
    if x is None or not math.isfinite(float(x)):
        return None
    return float(x)


def _artifact_metric_vectors(
    P: np.ndarray,
    Q_raw: np.ndarray,
    pred_expected: np.ndarray | None = None,
    Q_counts: np.ndarray | None = None,
) -> dict:
    Q_eps = np.vstack([smooth_pmf(q, EPS_PRIMARY) for q in Q_raw])
    Q_alt = np.vstack([smooth_pmf(q, EPS_ALT) for q in Q_raw])
    Q_lap = laplace_smooth_counts(Q_counts if Q_counts is not None else Q_raw, alpha=LAPLACE_ALPHA)
    rps_arr, cdf_sq, disagree = e5.rps_components(P, Q_eps)
    rps_raw, _, _ = e5.rps_components(P, Q_raw)
    mu = np.asarray(pred_expected, dtype=float) if pred_expected is not None else (Q_raw @ e5.GRID)
    h = P @ e5.GRID
    return {
        "rps": rps_arr,
        "rps_unsmoothed": rps_raw,
        "rps_cdf_sq": cdf_sq,
        "rps_disagree": disagree,
        "ce_eps1e6": e5.ce_per_artifact(P, Q_eps),
        "ce_eps1e3": e5.ce_per_artifact(P, Q_alt),
        "ce_laplace05": e5.ce_per_artifact(P, Q_lap),
        "tvd": e5.tvd_per_artifact(P, Q_raw),
        "brier6": e5.brier_per_artifact(P, Q_eps),
        "mu": mu,
        "h": h,
        "diff": mu - h,
    }


def _summarize_vectors(vecs: dict, idx: np.ndarray | None = None) -> dict[str, float | None]:
    sl = slice(None) if idx is None else idx
    mu, h, diff = vecs["mu"][sl], vecs["h"][sl], vecs["diff"][sl]
    corrs = e5.safe_correlations(mu, h)
    icca, iccc = e5.icc_a1_c1(mu, h)
    return {
        "rps": float(np.mean(vecs["rps"][sl])),
        "rps_unsmoothed": float(np.mean(vecs["rps_unsmoothed"][sl])),
        "rps_cdf_sq": float(np.mean(vecs["rps_cdf_sq"][sl])),
        "rps_disagree": float(np.mean(vecs["rps_disagree"][sl])),
        "ce_eps1e6": float(np.mean(vecs["ce_eps1e6"][sl])),
        "ce_eps1e3": float(np.mean(vecs["ce_eps1e3"][sl])),
        "ce_laplace05": float(np.mean(vecs["ce_laplace05"][sl])),
        "tvd": float(np.mean(vecs["tvd"][sl])),
        "brier6": float(np.mean(vecs["brier6"][sl])),
        "pearson": _clean_float(corrs["pearson"]),
        "spearman": _clean_float(corrs["spearman"]),
        "kendall": _clean_float(corrs["kendall_tau_b"]),
        "icc_a1": _clean_float(icca),
        "icc_c1": _clean_float(iccc),
        "mae_0_1": float(np.mean(np.abs(diff))),
        "nrmse_0_1": float(np.sqrt(np.mean(diff ** 2))),
        "signed_bias_0_1": float(np.mean(diff)),
        "mean_pred_0_1": float(np.mean(mu)),
        "mean_target_0_1": float(np.mean(h)),
    }


def task_cluster_bootstrap(
    P: np.ndarray,
    Q_raw: np.ndarray,
    tasks: np.ndarray,
    draws: int = BOOT_DRAWS,
    seed: int = SEED,
    resample_tasks_k: int | None = None,
    pred_expected: np.ndarray | None = None,
    baseline_Q_raw: np.ndarray | None = None,
    Q_counts: np.ndarray | None = None,
    baseline_Q_counts: np.ndarray | None = None,
) -> dict:
    """Cluster bootstrap resampling whole tasks (or k tasks) with replacement."""
    vecs = _artifact_metric_vectors(P, Q_raw, pred_expected=pred_expected, Q_counts=Q_counts)
    point = _summarize_vectors(vecs)
    bvecs = (
        _artifact_metric_vectors(P, baseline_Q_raw, Q_counts=baseline_Q_counts)
        if baseline_Q_raw is not None
        else None
    )
    base_point = _summarize_vectors(bvecs) if bvecs is not None else None

    unique_tasks = sorted(set(tasks.tolist()))
    positions = [np.flatnonzero(tasks == t) for t in unique_tasks]
    n_t = len(unique_tasks) if resample_tasks_k is None else int(resample_tasks_k)
    rng = np.random.default_rng(seed)

    keys = (
        "rps", "ce_eps1e6", "ce_eps1e3", "ce_laplace05", "tvd",
        "pearson", "spearman", "kendall", "icc_a1", "icc_c1",
        "mae_0_1", "nrmse_0_1", "signed_bias_0_1",
    )
    diff_keys = ("rps", "ce_eps1e6", "ce_laplace05", "tvd", "mae_0_1", "pearson", "spearman")
    samples: dict[str, list[float]] = {k: [] for k in keys}
    diff_samples: dict[str, list[float]] = {k: [] for k in diff_keys}

    for _ in range(draws):
        picked = rng.integers(0, len(unique_tasks), size=n_t)
        idx = np.concatenate([positions[i] for i in picked])
        m = _summarize_vectors(vecs, idx)
        for k in keys:
            if m[k] is not None:
                samples[k].append(float(m[k]))
        if bvecs is not None:
            mb = _summarize_vectors(bvecs, idx)
            for k in diff_keys:
                if m[k] is not None and mb[k] is not None:
                    diff_samples[k].append(float(m[k] - mb[k]))

    cis = {
        k: (
            {
                "point": point[k],
                "ci95": [lo := float(np.percentile(vs, 2.5)), hi := float(np.percentile(vs, 97.5))],
                "half_width": 0.5 * (hi - lo),
                "valid_draws": len(vs),
            }
            if vs
            else {"point": point[k], "ci95": None, "half_width": None, "valid_draws": 0}
        )
        for k, vs in samples.items()
    }
    out = {
        "n_artifacts": int(len(P)),
        "n_tasks_total": len(unique_tasks),
        "n_tasks_resampled": n_t,
        "draws": draws,
        "seed": seed,
        "point": point,
        "metrics": cis,
    }
    if base_point is not None:
        contrasts = {}
        for k, vs in diff_samples.items():
            p_diff = float(point[k] - base_point[k]) if (point[k] is not None and base_point[k] is not None) else None
            if vs:
                arr = np.asarray(vs, dtype=float)
                lo, hi = float(np.percentile(arr, 2.5)), float(np.percentile(arr, 97.5))
                p_two = float(2.0 * min(np.mean(arr <= 0.0), np.mean(arr >= 0.0)))
                contrasts[k] = {
                    "diff_point": p_diff,
                    "ci95": [lo, hi],
                    "p_val_two_sided": min(1.0, max(1.0 / (len(arr) + 1.0), p_two)),
                    "valid_draws": len(vs),
                }
            else:
                contrasts[k] = {"diff_point": p_diff, "ci95": None, "p_val_two_sided": None, "valid_draws": 0}
        out["baseline_point"] = base_point
        out["paired_minus_baseline"] = contrasts
    return out


def weighted_kappas_and_agreement(a: list[int], b: list[int]) -> dict[str, float | None]:
    """Compute exact match, within-1 agreement, linear-weighted and quadratic-weighted Cohen's kappa."""
    x, y = np.asarray(a), np.asarray(b)
    if x.ndim != 1 or x.shape != y.shape or not len(x):
        raise ValueError("Agreement requires nonempty, aligned rating vectors")
    for values in (x, y):
        if not np.isfinite(values).all() or np.any(values != values.astype(int)) or np.any((values < 0) | (values > 5)):
            raise ValueError("Agreement ratings must be integers in 0..5")
    x, y = x.astype(int), y.astype(int)
    n = len(x)
    o = np.zeros((6, 6), dtype=float)
    for xi, yi in zip(x, y):
        o[xi, yi] += 1.0
    o /= n
    e = o.sum(axis=1, keepdims=True) @ o.sum(axis=0, keepdims=True)
    idx = np.arange(6)[:, None] - np.arange(6)[None, :]

    def kappa(power: int) -> float | None:
        w = (np.abs(idx) ** power) / (5.0 ** power)
        denom = float(np.sum(w * e))
        # Equal constant raters have perfect observed agreement, but chance
        # agreement is also perfect: chance-corrected kappa is undefined (0/0).
        return None if denom == 0 else float(1.0 - np.sum(w * o) / denom)

    return {
        "exact_match": float(np.mean(x == y)),
        "within_1": float(np.mean(np.abs(x - y) <= 1)),
        "kappa_linear": kappa(1),
        "kappa_quadratic": kappa(2),
    }


def load_canonical_exp09() -> tuple[dict[str, dict], list[dict]]:
    """Load canonical 100-item catalog from A1 CSV (never reading sealed/) and all rated main CSV rows."""
    a1_path = EXP09_DIR / "ratings/Brando_Miranda__native_main_A1.csv"
    with a1_path.open(newline="") as fh:
        catalog = {
            row["item_id"].strip(): {
                "item_id": row["item_id"].strip(),
                "task_folder": row["task_folder"].strip(),
                "candidate_file": row["candidate_file"].strip(),
            }
            for row in csv.DictReader(fh)
        }
    assert len(catalog) == 100, f"Expected 100 canonical items, got {len(catalog)}"

    manifest = json.loads((EXP09_DIR / "ratings/RAW_MANIFEST.json").read_text())
    entries = [f for f in manifest["files"] if f.get("packet") == "native_main"]
    all_rows: list[dict] = []
    seen_pairs: set[tuple[str, str]] = set()
    for entry in entries:
        csv_path = EXP09_DIR / entry["path"]
        assert sha256_file(csv_path) == entry["sha256"], f"SHA mismatch on {entry['filename']}"
        with csv_path.open(newline="") as fh:
            for row in csv.DictReader(fh):
                rid, iid = row["rater_id"].strip(), row["item_id"].strip()
                assert iid in catalog, f"Unknown item_id {iid}"
                pair = (rid, iid)
                assert pair not in seen_pairs, f"Duplicate pair {pair}"
                seen_pairs.add(pair)
                row["_canonical_task"] = catalog[iid]["task_folder"]
                row["_canonical_cand"] = catalog[iid]["candidate_file"]
                row["_candidate_file_matches_canonical"] = row["candidate_file"].strip() == catalog[iid]["candidate_file"]
                all_rows.append(row)
    return catalog, all_rows


def section1_provenance_audit(catalog: dict[str, dict]) -> dict:
    """Compare Old 25 task IDs and provenance against New 25 (Exp 09) task IDs."""
    prov_csv = CERT_JUDGE_DIR / "experiments/41_paper_panel_provenance_audit_and_vb_expert_label_rescore/results/provenance_by_task.csv"
    with prov_csv.open(newline="") as fh:
        old_tasks = sorted({r["provenance100_current_task_id"].strip().lower() for r in csv.DictReader(fh) if r["provenance100_current_task_id"].strip()})

    ds = _load_old_dataset()
    old_tasks_ds = sorted({r["task"].strip().lower() for r in ds["rows"]})
    new_tasks = sorted({v["task_folder"] for v in catalog.values()})
    new_slugs = [t.split("_", 2)[2] for t in new_tasks]

    near_pairs = []
    for nt in new_tasks:
        n_toks = set(nt.split("_")[2:]) - {"algorithm", "of", "safe", "set", "layer", "service"}
        for ot in old_tasks_ds:
            o_toks = set(ot.replace("humaneval_", "").replace("_safe", "").split("_"))
            shared = sorted(w for w in (n_toks & o_toks) if len(w) > 2 and not w.isdigit())
            if shared:
                near_pairs.append({"new_task": nt, "old_task": ot, "shared_tokens": shared})

    exact_overlap = sorted(set(old_tasks_ds) & set(new_slugs))
    return {
        "old_25_task_count": len(old_tasks_ds),
        "old_25_certjudge_scored_task_count": len(old_tasks),
        "new_25_task_count": len(new_tasks),
        "exact_task_id_overlap": exact_overlap,
        "exact_overlap_count": len(exact_overlap),
        "near_topic_pairs": near_pairs,
        "old_25_provenance_summary": {
            "veribench_exp100_ref_drift_tasks": 9,
            "veribench_exp100_placeholder_tasks": 5,
            "certjudge_exp41_missing_gold_tasks": 1,
            "certjudge_exp41_matched_tasks": 7,
            "certjudge_exp41_mismatched_tasks": 17,
            "solver_distribution": "74/75 claude-3-7-sonnet-20250219 single-call temp 0.7 (no compiler loop); 1 missing receipt",
        },
        "new_25_provenance_summary": {
            "cohort_sha256": json.loads(
                (ROOT / "research_artifacts/09_human_rating_collection/preparation_11-09-2026/full_team_11-14-2026/COHORT_100_NATIVE_COMMITMENT.json").read_text()
            )["cohort_sha256"],
            "n_artifacts": len(catalog),
            "n_tasks": len(new_tasks),
            "agents_per_task": 4,
            "placeholder_ref_tasks": 0,
            "solver_distribution": "4 frontier native agents (Codex GPT-6 Astra, Claude Code Fable 5.1, Grok CLI 4.7, Antigravity CLI Gemini 4 Argon)",
        },
    }


def _summarize_rater_group(rows: list[dict]) -> dict:
    vals = [int(r["final_score_0_5"].strip()) for r in rows]
    mins = []
    for r in rows:
        try:
            mins.append(float(r["minutes_spent"].strip()))
        except ValueError:
            pass
    return {
        "rater_name": rows[0]["rater_name"].strip(),
        "n_numeric": len(vals),
        "mean_0_5": float(np.mean(vals)),
        "mean_0_1": float(np.mean(vals) / 5.0),
        "sd_0_5": float(np.std(vals, ddof=1)) if len(vals) > 1 else 0.0,
        "histogram_0_5": {str(k): vals.count(k) for k in range(6)},
        "share_4_or_5": float(sum(v >= 4 for v in vals) / len(vals)),
        "attestation_counts": dict(sorted(Counter(r["ai_assisted_rating_attestation (AI help is allowed)"].strip() for r in rows).items())),
        "confidence_counts": dict(sorted(Counter(r["confidence"].strip() for r in rows).items())),
        "minutes_entries": len(mins),
        "minutes_median": float(statistics.median(mins)) if mins else None,
        "minutes_mean": float(np.mean(mins)) if mins else None,
        "minutes_range": [float(min(mins)), float(max(mins))] if mins else None,
    }


def _compute_loro_ceiling(catalog: dict[str, dict], by_item: dict[str, list[tuple[str, int]]]) -> dict[str, float]:
    disagree_terms, unbiased_noise_terms = [], []
    loro_rps_per_item, loro_ce_per_item, loro_tvd_per_item = [], [], []
    for iid in sorted(catalog):
        rlist = by_item[iid]
        m = len(rlist)
        if m < 2:
            raise ValueError(f"Leave-one-rater-out scoring requires at least two ratings for {iid}")
        counts = np.zeros(6, dtype=float)
        for _, val in rlist:
            counts[val] += 1.0
        pc = np.cumsum(counts / m)[:5]
        disagree = float(np.mean(pc * (1.0 - pc)))
        disagree_terms.append(disagree)
        unbiased_noise_terms.append(disagree / (m - 1) if m > 1 else 0.0)
        item_rps, item_ce, item_tvd = [], [], []
        for _, val_h in rlist:
            # Remove one count of val_h for leave-one-rater-out empirical forecast
            q_cnt = counts.copy()
            q_cnt[val_h] -= 1.0
            q_raw = q_cnt / (m - 1)
            q_lap = (q_cnt + LAPLACE_ALPHA) / ((m - 1) + 6.0 * LAPLACE_ALPHA)
            p_h = one_hot_pmf(val_h)[None, :]
            item_rps.append(float(e5.rps_components(p_h, q_raw[None, :])[0][0]))
            item_ce.append(float(e5.ce_per_artifact(p_h, q_lap[None, :])[0]))
            item_tvd.append(float(e5.tvd_per_artifact(p_h, q_raw[None, :])[0]))
        loro_rps_per_item.append(float(np.mean(item_rps)))
        loro_ce_per_item.append(float(np.mean(item_ce)))
        loro_tvd_per_item.append(float(np.mean(item_tvd)))
    return {
        "mean_rps": float(np.mean(loro_rps_per_item)),
        "mean_ce_laplace05": float(np.mean(loro_ce_per_item)),
        "mean_tvd": float(np.mean(loro_tvd_per_item)),
        "empirical_disagreement_floor_rps": float(np.mean(disagree_terms)),
        "unbiased_finite_sample_noise_term_s2_over_m": float(np.mean(unbiased_noise_terms)),
    }


def section2_live_ratings_and_ceiling(catalog: dict[str, dict], all_rows: list[dict]) -> tuple[dict, dict[str, list[tuple[str, int]]]]:
    """Audit live Exp 09 scores, checklist, attestations, and compute inter-rater human ceiling."""
    scored_rows = [r for r in all_rows if r["final_score_0_5"].strip() in {"0", "1", "2", "3", "4", "5"}]
    na_rows = [r for r in all_rows if r["final_score_0_5"].strip().upper() == "N/A"]

    by_rater: dict[str, list[dict]] = {}
    by_item: dict[str, list[tuple[str, int]]] = {}
    checklist_scores: dict[tuple[str, str, str, str], list[int]] = {}
    anomalies = []

    for r in scored_rows:
        rid = r["rater_id"].strip()
        val = int(r["final_score_0_5"].strip())
        by_rater.setdefault(rid, []).append(r)
        by_item.setdefault(r["item_id"].strip(), []).append((rid, val))
        key = (
            r["A_key_gold_theorems_covered (Y/N)"].strip(),
            r["B_gold_pre_postconditions_preserved_or_strengthened (Y/N)"].strip(),
            r["C_obvious_theorem_spam (Y/N)"].strip(),
            r["D_spam_handful_or_dominates (none/handful/dominates)"].strip(),
        )
        checklist_scores.setdefault(key, []).append(val)
        if not r["_candidate_file_matches_canonical"]:
            anomalies.append({
                "rater_id": rid,
                "item_id": r["item_id"].strip(),
                "canonical_candidate_file": r["_canonical_cand"],
                "raw_candidate_file": r["candidate_file"].strip(),
            })

    rater_maps = {
        rid: {r["item_id"].strip(): int(r["final_score_0_5"].strip()) for r in rows}
        for rid, rows in by_rater.items()
    }

    def pairwise_stats(pred_rid: str, targ_rid: str) -> dict:
        shared = sorted(set(rater_maps[pred_rid]) & set(rater_maps[targ_rid]))
        tasks = np.array([catalog[iid]["task_folder"] for iid in shared])
        P = np.vstack([one_hot_pmf(rater_maps[targ_rid][iid]) for iid in shared])
        Q = np.vstack([one_hot_pmf(rater_maps[pred_rid][iid]) for iid in shared])
        return {
            "pred_rater": pred_rid,
            "target_rater": targ_rid,
            "n_shared_items": len(shared),
            "n_shared_tasks": int(len(set(tasks.tolist()))),
            "agreement": weighted_kappas_and_agreement(
                [rater_maps[pred_rid][iid] for iid in shared],
                [rater_maps[targ_rid][iid] for iid in shared],
            ),
            "bootstrap": task_cluster_bootstrap(P, Q, tasks, draws=BOOT_DRAWS, seed=SEED),
        }

    all_vals = [int(r["final_score_0_5"].strip()) for r in scored_rows]
    summary = {
        "n_artifacts": len(catalog),
        "n_tasks": len({v["task_folder"] for v in catalog.values()}),
        "n_numeric_ratings": len(scored_rows),
        "n_not_applicable_rows": len(na_rows),
        "n_active_raters": len(by_rater),
        "artifact_rater_coverage_counts": {str(k): v for k, v in sorted(Counter(len(v) for v in by_item.values()).items())},
        "overall_histogram_0_5": {str(k): all_vals.count(k) for k in range(6)},
        "overall_mean_0_5": float(np.mean(all_vals)),
        "overall_mean_0_1": float(np.mean(all_vals) / 5.0),
        "overall_share_4_or_5": float(sum(v >= 4 for v in all_vals) / len(all_vals)),
        "per_rater": {rid: _summarize_rater_group(by_rater[rid]) for rid in sorted(by_rater)},
        "checklist_profiles": [
            {
                "A_key_covered": k[0], "B_pre_post": k[1], "C_spam": k[2], "D_spam_extent": k[3],
                "count": len(vs), "mean_score_0_5": float(np.mean(vs)),
                "min_score": int(min(vs)), "max_score": int(max(vs)),
            }
            for k, vs in sorted(checklist_scores.items(), key=lambda kv: -len(kv[1]))
        ],
        "identity_cell_anomalies": anomalies,
        "human_ceiling": {
            "T08_Amy_predicting_T05_Sri_100files": pairwise_stats("T08", "T05"),
            "T05_Sri_predicting_T08_Amy_100files": pairwise_stats("T05", "T08"),
            "T12_Rakshit_vs_T05_Sri_30files": pairwise_stats("T12", "T05"),
            "T12_Rakshit_vs_T08_Amy_30files": pairwise_stats("T12", "T08"),
            "T06_Donald_vs_T05_Sri_16files": pairwise_stats("T06", "T05"),
            "T06_Donald_vs_T08_Amy_16files": pairwise_stats("T06", "T08"),
            "loro_all_100_items_artifact_weighted": _compute_loro_ceiling(catalog, by_item),
        },
    }
    return summary, by_item


def _theorem_baseline_predictions(catalog: dict[str, dict], public_only: bool = False) -> tuple[np.ndarray, list[float]]:
    main_task_dir = EXP09_DIR / "rating_task_packet/main_rating_task"
    gold_counts: dict[str, int] = {}
    ratios: list[float] = []
    q_rows = []
    for iid in sorted(catalog):
        tf = catalog[iid]["task_folder"]
        if tf not in gold_counts:
            g_src = (main_task_dir / tf / "gold_lean/reference.lean").read_text()
            gold_counts[tf] = count_theorems(g_src, public_only=public_only)
            assert gold_counts[tf] > 0, tf
        c_src = (main_task_dir / catalog[iid]["candidate_file"]).read_text()
        ratio = min(1.0, count_theorems(c_src, public_only=public_only) / gold_counts[tf])
        ratios.append(ratio)
        q_rows.append(linear_interp_pmf(5.0 * ratio))
    return np.vstack(q_rows), ratios


def section3_zero_cost_baselines(catalog: dict[str, dict], by_item: dict[str, list[tuple[str, int]]]) -> dict:
    """Evaluate zero-cost constant and theorem-count baselines on Exp 09 (100 files, 25 tasks)."""
    items_sorted = sorted(catalog)
    tasks = np.array([catalog[iid]["task_folder"] for iid in items_sorted])
    P = e5.counts_from_ratings([[v for _, v in by_item[iid]] for iid in items_sorted])
    P = P / P.sum(axis=1, keepdims=True)

    ds = _load_old_dataset()
    p_train_counts = e5.counts_from_ratings([r["ratings"] for r in ds["rows"] if r["split"] == "train"])
    old_train_marginal = (p_train_counts / p_train_counts.sum(axis=1, keepdims=True)).mean(axis=0)
    Q_old_const = np.broadcast_to(old_train_marginal, (len(P), 6)).copy()
    Q_old_counts = len(p_train_counts) * Q_old_const

    in_sample_marginal = P.mean(axis=0)
    Q_insample_const = np.broadcast_to(in_sample_marginal, (len(P), 6)).copy()
    Q_insample_counts = len(P) * Q_insample_const

    Q_thm_all, ratios_all = _theorem_baseline_predictions(catalog, public_only=False)
    Q_thm_pub, ratios_pub = _theorem_baseline_predictions(catalog, public_only=True)

    return {
        "old_25_train_marginal_pmf": [float(x) for x in old_train_marginal],
        "exp09_in_sample_marginal_pmf": [float(x) for x in in_sample_marginal],
        "old_train_constant_baseline": task_cluster_bootstrap(
            P, Q_old_const, tasks, draws=BOOT_DRAWS, seed=SEED, Q_counts=Q_old_counts
        ),
        "in_sample_constant_reference_only": task_cluster_bootstrap(
            P, Q_insample_const, tasks, draws=BOOT_DRAWS, seed=SEED, Q_counts=Q_insample_counts
        ),
        "theorem_count_ratio_all_declarations": {
            "mean_ratio": float(np.mean(ratios_all)),
            "fraction_ratio_eq_1": float(np.mean([r >= 1.0 - 1e-12 for r in ratios_all])),
            "vs_old_train_constant": task_cluster_bootstrap(
                P, Q_thm_all, tasks, draws=BOOT_DRAWS, seed=SEED,
                baseline_Q_raw=Q_old_const, baseline_Q_counts=Q_old_counts,
            ),
            "vs_in_sample_constant": task_cluster_bootstrap(
                P, Q_thm_all, tasks, draws=BOOT_DRAWS, seed=SEED,
                baseline_Q_raw=Q_insample_const, baseline_Q_counts=Q_insample_counts,
            ),
        },
        "theorem_count_ratio_public_only_sensitivity": {
            "mean_ratio": float(np.mean(ratios_pub)),
            "fraction_ratio_eq_1": float(np.mean([r >= 1.0 - 1e-12 for r in ratios_pub])),
            "vs_old_train_constant": task_cluster_bootstrap(
                P, Q_thm_pub, tasks, draws=BOOT_DRAWS, seed=SEED,
                baseline_Q_raw=Q_old_const, baseline_Q_counts=Q_old_counts,
            ),
        },
    }


def _extract_exp22_splits() -> dict:
    agg22 = json.loads((EXP22_DIR / "results/aggregates_5metrics.json").read_text())
    pa = agg22["panel_a_exp100_selected_judge"]
    return {
        sp: {
            "n_artifacts": pa["splits"][sp]["n_artifacts"],
            "n_tasks": pa["splits"][sp]["n_tasks"],
            "n_ratings": pa["splits"][sp]["n_ratings"],
            "member_median_scalar": {
                "spearman": pa["splits"][sp]["exp100_selected_member_median_scalar"]["point"]["spearman"],
                "pearson": pa["splits"][sp]["exp100_selected_member_median_scalar"]["point"]["pearson"],
                "kendall_tau_b": pa["splits"][sp]["exp100_selected_member_median_scalar"]["point"]["kendall_tau_b"],
                "rps": pa["splits"][sp]["exp100_selected_member_median_scalar"]["point"]["rps"],
                "ce": pa["splits"][sp]["exp100_selected_member_median_scalar"]["point"]["ce"],
                "tvd": pa["splits"][sp]["exp100_selected_member_median_scalar"]["point"]["tvd"],
                "mae_0_1": pa["splits"][sp]["exp100_selected_member_median_scalar"]["point"]["mae_0_1"],
                "signed_bias_0_1": pa["splits"][sp]["exp100_selected_member_median_scalar"]["point"]["signed_bias_0_1"],
                "judge_mean_0_1": pa["splits"][sp]["exp100_selected_member_median_scalar"]["point"]["judge_mean_0_1"],
                "human_mean_0_1": pa["splits"][sp]["exp100_selected_member_median_scalar"]["point"]["human_mean_0_1"],
                "mse_decomp": pa["splits"][sp]["exp100_selected_member_median_scalar"]["point"]["mse_decomposition"],
                "intervals_95": {
                    k: pa["splits"][sp]["exp100_selected_member_median_scalar"]["intervals_95"][k]
                    for k in ("rps", "ce", "tvd", "pearson", "spearman", "kendall_tau_b", "signed_bias_0_1")
                },
            },
            "pmf_mean_scalar": {
                "spearman": pa["splits"][sp]["exp100_selected_pmf_mean_scalar"]["point"]["spearman"],
                "pearson": pa["splits"][sp]["exp100_selected_pmf_mean_scalar"]["point"]["pearson"],
                "rps": pa["splits"][sp]["exp100_selected_pmf_mean_scalar"]["point"]["rps"],
                "signed_bias_0_1": pa["splits"][sp]["exp100_selected_pmf_mean_scalar"]["point"]["signed_bias_0_1"],
                "judge_mean_0_1": pa["splits"][sp]["exp100_selected_pmf_mean_scalar"]["point"]["judge_mean_0_1"],
                "human_mean_0_1": pa["splits"][sp]["exp100_selected_pmf_mean_scalar"]["point"]["human_mean_0_1"],
                "intervals_95": {
                    k: pa["splits"][sp]["exp100_selected_pmf_mean_scalar"]["intervals_95"][k]
                    for k in ("rps", "ce", "tvd", "pearson", "spearman", "kendall_tau_b", "signed_bias_0_1")
                },
                "paired_minus_constant_rps": pa["splits"][sp]["exp100_selected_pmf_mean_scalar"]["paired_minus_baseline"]["rps"],
            },
            "constant_rps": pa["splits"][sp]["constant_train_marginal"]["point"]["rps"],
            "constant_ce": pa["splits"][sp]["constant_train_marginal"]["point"]["ce"],
            "constant_tvd": pa["splits"][sp]["constant_train_marginal"]["point"]["tvd"],
            "constant_intervals_95": {
                k: pa["splits"][sp]["constant_train_marginal"]["intervals_95"][k]
                for k in ("rps", "ce", "tvd")
            },
        }
        for sp in ("train", "val", "test", "test_ordinary", "all_75")
    }


def _compute_simpson_pooling(P_emp: np.ndarray, tasks_100: np.ndarray) -> dict:
    ds = _load_old_dataset()
    p_old_cnt = e5.counts_from_ratings([r["ratings"] for r in ds["rows"]])
    P_old = p_old_cnt / p_old_cnt.sum(axis=1, keepdims=True)
    tasks_old = np.array([f"old__{r['task']}" for r in ds["rows"]])

    P_pool = np.vstack([P_old, P_emp])
    Q_pool = np.vstack([
        np.broadcast_to(P_old.mean(axis=0), (len(P_old), 6)).copy(),
        np.broadcast_to(P_emp.mean(axis=0), (len(P_emp), 6)).copy(),
    ])
    Q_pool_counts = np.vstack([
        len(P_old) * np.broadcast_to(P_old.mean(axis=0), (len(P_old), 6)),
        len(P_emp) * np.broadcast_to(P_emp.mean(axis=0), (len(P_emp), 6)),
    ])
    Q_pool_global = np.broadcast_to(P_pool.mean(axis=0), (len(P_pool), 6)).copy()
    Q_pool_global_counts = len(P_pool) * Q_pool_global
    tasks_pool = np.concatenate([tasks_old, np.array([f"new__{t}" for t in tasks_100])])

    pool_boot = task_cluster_bootstrap(
        P_pool, Q_pool, tasks_pool, draws=BOOT_DRAWS, seed=SEED, Q_counts=Q_pool_counts
    )
    pool_vs_global = task_cluster_bootstrap(
        P_pool, Q_pool, tasks_pool, draws=BOOT_DRAWS, seed=SEED,
        baseline_Q_raw=Q_pool_global, Q_counts=Q_pool_counts, baseline_Q_counts=Q_pool_global_counts,
    )
    return {
        "n_old_artifacts": int(len(P_old)),
        "n_new_artifacts": int(len(P_emp)),
        "n_pooled_artifacts": int(len(P_pool)),
        "n_pooled_tasks": int(len(set(tasks_pool.tolist()))),
        "old_mean_human_0_1": float((P_old @ e5.GRID).mean()),
        "new_mean_human_0_1": float((P_emp @ e5.GRID).mean()),
        "within_old_correlation": None,
        "within_new_correlation": None,
        "within_cohort_correlation_status": "undefined: the forecast is constant within each cohort",
        "pooled_metrics": pool_boot["metrics"],
        "pooled_regime_vs_global_constant": pool_vs_global["paired_minus_baseline"],
    }


def section4_06_08_08_and_pooling_and_ci_scaling(
    catalog: dict[str, dict],
    by_item: dict[str, list[tuple[str, int]]],
    all_rows: list[dict],
) -> dict:
    """Reproduce Exp 22 '0.6/0.8/0.8' diagnosis, measure 10-vs-25 task CI widths, and show Simpson's paradox."""
    scored_by_rater: dict[str, dict[str, int]] = {}
    for r in all_rows:
        s = r["final_score_0_5"].strip()
        if s in {"0", "1", "2", "3", "4", "5"}:
            scored_by_rater.setdefault(r["rater_id"].strip(), {})[r["item_id"].strip()] = int(s)

    items_sorted = sorted(catalog)
    tasks_100 = np.array([catalog[iid]["task_folder"] for iid in items_sorted])
    P_t05 = np.vstack([one_hot_pmf(scored_by_rater["T05"][iid]) for iid in items_sorted])
    Q_t08 = np.vstack([one_hot_pmf(scored_by_rater["T08"][iid]) for iid in items_sorted])
    Q_thm, _ = _theorem_baseline_predictions(catalog, public_only=False)
    P_emp = e5.counts_from_ratings([[v for _, v in by_item[iid]] for iid in items_sorted])
    P_emp = P_emp / P_emp.sum(axis=1, keepdims=True)

    return {
        "old_25_06_08_08_splits": _extract_exp22_splits(),
        "ci_width_scaling_10_vs_25_tasks": {
            "human_T08_vs_T05": {
                "k10": task_cluster_bootstrap(P_t05, Q_t08, tasks_100, draws=BOOT_DRAWS, seed=SEED, resample_tasks_k=10)["metrics"],
                "k25": task_cluster_bootstrap(P_t05, Q_t08, tasks_100, draws=BOOT_DRAWS, seed=SEED, resample_tasks_k=25)["metrics"],
            },
            "theorem_count_baseline": {
                "k10": task_cluster_bootstrap(P_emp, Q_thm, tasks_100, draws=BOOT_DRAWS, seed=SEED, resample_tasks_k=10)["metrics"],
                "k25": task_cluster_bootstrap(P_emp, Q_thm, tasks_100, draws=BOOT_DRAWS, seed=SEED, resample_tasks_k=25)["metrics"],
            },
        },
        "simpson_paradox_regime_only_pooling": _compute_simpson_pooling(P_emp, tasks_100),
    }


def _batch_pearson(X: np.ndarray, Y: np.ndarray) -> np.ndarray:
    """Row-wise Pearson correlation on 2D arrays (B, n); returns NaN where variance is 0."""
    xc = X - X.mean(axis=1, keepdims=True)
    yc = Y - Y.mean(axis=1, keepdims=True)
    denom = np.sqrt(np.sum(xc * xc, axis=1) * np.sum(yc * yc, axis=1))
    out = np.full(X.shape[0], np.nan, dtype=float)
    valid = (denom > 0.0) & (np.ptp(X, axis=1) > 1e-12) & (np.ptp(Y, axis=1) > 1e-12)
    out[valid] = np.clip(np.sum(xc[valid] * yc[valid], axis=1) / denom[valid], -1.0, 1.0)
    return out


def _batch_spearman(X: np.ndarray, Y: np.ndarray) -> np.ndarray:
    """Row-wise tie-aware Spearman rank correlation on 2D arrays (B, n)."""
    return _batch_pearson(rankdata(X, method="average", axis=1), rankdata(Y, method="average", axis=1))


def _batch_kendall_tau_b(X: np.ndarray, Y: np.ndarray) -> np.ndarray:
    """Row-wise tie-aware Kendall tau-b on 2D arrays (B, n); returns NaN where undefined."""
    n = X.shape[1]
    iu, ju = np.triu_indices(n, k=1)
    out = np.full(X.shape[0], np.nan, dtype=float)
    for start in range(0, X.shape[0], 2000):
        xb = X[start : start + 2000]
        yb = Y[start : start + 2000]
        sx = np.sign(xb[:, ju] - xb[:, iu]).astype(np.int8)
        sy = np.sign(yb[:, ju] - yb[:, iu]).astype(np.int8)
        num = np.sum(sx * sy, axis=1, dtype=np.int64)
        nz_x = np.sum(sx != 0, axis=1, dtype=np.float64)
        nz_y = np.sum(sy != 0, axis=1, dtype=np.float64)
        denom = np.sqrt(nz_x * nz_y)
        valid = denom > 0.0
        vals = np.full(xb.shape[0], np.nan, dtype=float)
        vals[valid] = np.clip(num[valid] / denom[valid], -1.0, 1.0)
        out[start : start + 2000] = vals
    return out


def _corr_ci_perm(xs: list[float], ys: list[float], method: str, draws: int = PERM_DRAWS, seed: int = SEED) -> dict:
    """Compute correlation, 95% unit bootstrap CI, and one-sided permutation p-value."""
    x_arr = np.asarray(xs, dtype=float)
    y_arr = np.asarray(ys, dtype=float)
    n = len(x_arr)
    if method == "pearson":
        obs = _clean_float(e5.safe_correlations(x_arr, y_arr)["pearson"])
        batch_fn = _batch_pearson
    elif method == "spearman":
        obs = _clean_float(e5.safe_correlations(x_arr, y_arr)["spearman"])
        batch_fn = _batch_spearman
    elif method == "kendall":
        obs = _clean_float(e5.safe_correlations(x_arr, y_arr)["kendall_tau_b"])
        batch_fn = _batch_kendall_tau_b
    else:
        raise ValueError(f"Unknown correlation method: {method}")

    if obs is None or n < 3:
        return {"n": n, "value": obs, "ci95": None, "perm_p_one_sided": None}

    rng = np.random.default_rng(seed)
    idx = rng.integers(0, n, size=(draws, n))
    boot_vals = batch_fn(x_arr[idx], y_arr[idx])
    valid_boot = boot_vals[np.isfinite(boot_vals)]
    ci95 = (
        [float(np.percentile(valid_boot, 2.5)), float(np.percentile(valid_boot, 97.5))]
        if len(valid_boot) > 0
        else None
    )

    perm_cols = np.argsort(rng.random((draws, n)), axis=1)
    perm_vals = batch_fn(np.broadcast_to(x_arr, (draws, n)), y_arr[perm_cols])
    valid_perm = perm_vals[np.isfinite(perm_vals)]
    k = int(np.sum(valid_perm >= obs - 1e-12))
    return {
        "n": n,
        "value": float(obs),
        "ci95": ci95,
        "perm_p_one_sided": float((k + 1) / (len(valid_perm) + 1)),
    }


def _score_e39_unit(harvest_path: Path, unit: dict, heldout_items: list[str], ds_by_item: dict) -> dict[str, float] | None:
    h = json.loads(harvest_path.read_text())
    cells: dict[str, list[float]] = {}
    for c in h["cells"]:
        if c["kind"] == "crit" and c["status"] in ("measured", "deterministic") and c.get("score") is not None:
            cells.setdefault(c["item"], []).append(float(c["score"]))
    xs_med, ys_mean, p_rows, q_cnt_rows, q_raw_rows = [], [], [], [], []
    exact_tvd: list[Fraction] = []
    for it in heldout_items:
        reps = cells.get(it, [])
        if not reps:
            continue
        hum_r = ds_by_item[it]["ratings"]
        xs_med.append(float(statistics.median(reps)))
        ys_mean.append(sum(hum_r) / (5.0 * len(hum_r)))
        q_cnt = np.zeros(6, dtype=float)
        for s in reps:
            q_cnt[min(5, max(0, math.floor(5.0 * s + 0.5 + 1e-12)))] += 1.0
        p_cnt = np.zeros(6, dtype=float)
        for hr in hum_r:
            p_cnt[int(hr)] += 1.0
        p_rows.append(p_cnt / p_cnt.sum())
        q_cnt_rows.append(q_cnt)
        q_raw_rows.append(q_cnt / q_cnt.sum())
        exact_tvd.append(_exact_tvd_from_counts(p_cnt, q_cnt))
    if len(xs_med) < math.ceil(0.9 * len(heldout_items)):
        return None
    P = np.vstack(p_rows)
    Q_raw = np.vstack(q_raw_rows)
    Q_eps = np.vstack([smooth_pmf(q, EPS_PRIMARY) for q in Q_raw])
    Q_lap = laplace_smooth_counts(q_cnt_rows, alpha=LAPLACE_ALPHA)
    return {
        "n_items": len(xs_med),
        "saved_spearman": _clean_float(unit["criteria"]["heldout"]["spearman"]),
        "recomputed_spearman": _clean_float(e5.safe_correlations(np.asarray(xs_med), np.asarray(ys_mean))["spearman"]),
        "neg_rps": -float(np.mean(e5.rps_components(P, Q_raw)[0])),
        "neg_ce_laplace05": -float(np.mean(e5.ce_per_artifact(P, Q_lap))),
        "neg_ce_eps1e6": -float(np.mean(e5.ce_per_artifact(P, Q_eps))),
        # Average rational count ratios before converting to float so equal
        # TVDs stay tied in Spearman/Kendall, regardless of summation order.
        "neg_tvd": -float(sum(exact_tvd) / len(exact_tvd)),
        "neg_mae": -float(np.mean(np.abs(np.asarray(xs_med) - np.asarray(ys_mean)))),
    }


def _exact_tvd_from_counts(p_counts: np.ndarray, q_counts: np.ndarray) -> Fraction:
    """Exact TVD for observed integer histograms; preserves mathematical ties."""
    counts = (np.asarray(p_counts), np.asarray(q_counts))
    for values in counts:
        if values.shape != (6,) or not np.isfinite(values).all() or np.any(values < 0) or np.any(values != values.astype(int)) or values.sum() <= 0:
            raise ValueError("TVD requires nonempty six-category integer histograms")
    p, q = counts
    np_, nq = int(p.sum()), int(q.sum())
    return sum(abs(Fraction(int(pc), np_) - Fraction(int(qc), nq)) for pc, qc in zip(p, q)) / 2


def score_exp39_bridge() -> dict:
    """Reproduce the bridge from Experiment 39 receipts and the historical dataset only."""
    e39_res = CERT_JUDGE_DIR / "experiments/39_label_free_proxy_index_train_val_test_over_judge_families/results"
    utv = json.loads((e39_res / "units_train_val.json").read_text())["units"]
    ut = json.loads((e39_res / "units_test.json").read_text())["units"]
    all_units = utv + ut

    ds = _load_old_dataset()
    ds_by_item = {r["item"]: r for r in ds["rows"]}
    heldout_items = [r["item"] for r in ds["rows"] if r["split"] in ("val", "test")]
    assert len(heldout_items) == 45

    unit_scores = {}
    for u in all_units:
        scored = _score_e39_unit(e39_res / "harvest" / (u["config"].replace("|", "__") + ".json"), u, heldout_items, ds_by_item)
        if scored is not None:
            unit_scores[u["config"]] = scored

    assert abs(unit_scores["opus55x|H2"]["saved_spearman"] - unit_scores["opus55x|H2"]["recomputed_spearman"]) < 1e-12

    proxies = ("C_ms_gold", "TI_var_trainnorm", "PTI_v0_frozen")
    criteria = ("saved_spearman", "neg_rps", "neg_ce_laplace05", "neg_ce_eps1e6", "neg_tvd", "neg_mae")
    split_defs = {
        "train_llm": [u for u in all_units if u["split"] == "train" and u["kind"] == "llm"],
        "val_llm": [u for u in all_units if u["split"] == "val" and u["kind"] == "llm"],
        "test": [u for u in all_units if u["split"] == "test"],
        "all_llm": [u for u in all_units if u["kind"] == "llm"],
    }
    matrix: dict[str, dict] = {}
    for sp_name, ulist in split_defs.items():
        sp_matrix: dict[str, dict] = {}
        for prox in proxies:
            prox_matrix: dict[str, dict] = {}
            for crit_k in criteria:
                pairs = [
                    (float(u["indices"][prox]), float(unit_scores[u["config"]][crit_k]))
                    for u in ulist
                    if u["indices"].get(prox) is not None
                    and u["config"] in unit_scores
                    and unit_scores[u["config"]].get(crit_k) is not None
                ]
                xs = [a for a, _ in pairs]
                ys = [b for _, b in pairs]
                prox_matrix[crit_k] = {
                    "spearman": _corr_ci_perm(xs, ys, "spearman", draws=PERM_DRAWS, seed=SEED),
                    "kendall": _corr_ci_perm(xs, ys, "kendall", draws=PERM_DRAWS, seed=SEED),
                    "pearson": _corr_ci_perm(xs, ys, "pearson", draws=PERM_DRAWS, seed=SEED),
                }
            sp_matrix[prox] = prox_matrix
        matrix[sp_name] = sp_matrix

    gate_g0_val = matrix["test"]["C_ms_gold"]["saved_spearman"]["spearman"]["value"]
    assert abs(gate_g0_val - 0.557795) < 0.002, f"Gate G0 mismatch: {gate_g0_val}"
    return {
        "exp39_gate_g0_verified": {
            "opus55x_H2_saved_vs_recomputed_diff": abs(
                unit_scores["opus55x|H2"]["saved_spearman"] - unit_scores["opus55x|H2"]["recomputed_spearman"]
            ),
            "c_ms_gold_test_spearman": gate_g0_val,
            "c_ms_gold_test_n": matrix["test"]["C_ms_gold"]["saved_spearman"]["spearman"]["n"],
        },
        "exp39_item_coverage": {
            "heldout_items": len(heldout_items),
            "scored_configurations": len(unit_scores),
            "configurations_by_scored_item_count": dict(sorted(Counter(str(s["n_items"]) for s in unit_scores.values()).items())),
            "scoring_policy": "available items per configuration; at least 90% coverage, not a common complete panel",
        },
        "exp39_proxy_vs_proper_metrics": matrix,
    }


def section5_cert_judge_bridge() -> dict:
    """Evaluate Experiment 39, then attach the separately saved Experiment 51 reference."""
    result = score_exp39_bridge()
    result["exp51_n8_reference"] = json.loads(
        (CERT_JUDGE_DIR / "experiments/archive/51_certjudge_rescore_rps_ce_tvd_nov2026/rescore_proper_results.json").read_text()
    )
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--out", type=Path, default=EXP26_DIR / "results/summary_old_vs_new_11-24-2026.json")
    args = parser.parse_args()

    catalog, all_rows = load_canonical_exp09()
    s1 = section1_provenance_audit(catalog)
    s2, by_item = section2_live_ratings_and_ceiling(catalog, all_rows)
    s3 = section3_zero_cost_baselines(catalog, by_item)
    s4 = section4_06_08_08_and_pooling_and_ci_scaling(catalog, by_item, all_rows)
    s5 = section5_cert_judge_bridge()

    out = {
        "experiment": EXP26_DIR.name,
        "date": "11-24-2026",
        "compute": "CPU-only, $0.00 API spend, no DT, not Lean-checked proofs",
        "seed": SEED,
        "bootstrap_draws": BOOT_DRAWS,
        "section1_disjointness_and_provenance": s1,
        "section2_exp09_ratings_and_human_ceiling": s2,
        "section3_exp09_zero_cost_baselines": s3,
        "section4_why_06_08_08_and_pooling_and_ci_scaling": s4,
        "section5_cert_judge_5metric_bridge": s5,
    }
    assert_no_private_leak(out)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2) + "\n")
    print(f"Wrote {args.out}")
    print(json.dumps({
        "n_main_ratings": s2["n_numeric_ratings"],
        "T08_vs_T05_rps": s2["human_ceiling"]["T08_Amy_predicting_T05_Sri_100files"]["bootstrap"]["metrics"]["rps"],
        "T08_vs_T05_spearman": s2["human_ceiling"]["T08_Amy_predicting_T05_Sri_100files"]["bootstrap"]["metrics"]["spearman"],
        "old_const_rps": s3["old_train_constant_baseline"]["metrics"]["rps"],
        "thm_count_rps": s3["theorem_count_ratio_all_declarations"]["vs_old_train_constant"]["metrics"]["rps"],
        "simpson_pooled_pearson": s4["simpson_paradox_regime_only_pooling"]["pooled_metrics"]["pearson"],
        "exp39_c_ms_gold_test_neg_rps": s5["exp39_proxy_vs_proper_metrics"]["test"]["C_ms_gold"]["neg_rps"]["spearman"],
    }, indent=2))


if __name__ == "__main__":
    main()
