#!/usr/bin/env python3
"""Recompute QA_TASK.md from qa_input.json. Writes qa_cursor_high.json.

Forecasts: final_Q, constant per set, pooled constant, uniform, H2.
Test subsets: pooled, old, new. Bootstrap: 10000 task resamples, seed 20261124.
"""

import json
import math
from collections import defaultdict

import numpy as np
from scipy.optimize import minimize
from scipy.stats import pearsonr, spearmanr

EPS = 1e-6
MIN_GAP = 1e-12
N_BOOT = 10000
BOOT_SEED = 20261124
IN_PATH = "qa_input.json"
OUT_PATH = "qa_cursor_high.json"
SCORES = np.arange(6, dtype=float)
METRIC_NAMES = ("rps", "ce", "tvd")
FORECAST_NAMES = (
    "final_Q",
    "constant_per_set",
    "pooled_constant",
    "uniform",
    "h2",
)
SKIP_CORR = frozenset(("constant_per_set", "pooled_constant", "uniform"))

LIMITATIONS = [
    "RPS is the mean of five terms, k=0..4: (CQ_k-CP_k)^2 + CP_k*(1-CP_k). The second term depends only on the human histogram, so it cancels in paired RPS differences and remains in the reported RPS levels.",
    "Constant forecasts are histograms of every individual train+val rating in the pool (equal weight per rating), floored at 1e-6 and renormalised. They are not means of per-artifact histograms.",
    "H2 is the per-artifact histogram of concatenated astra and opus scores, floored at 1e-6 and renormalised. h3 is not included in H2.",
    "CE floors every forecast at 1e-6 and renormalises, then uses natural log. RPS, TVD, and forecast means use the forecast before that CE-only floor. Constant and H2 forecasts are already floored by definition.",
    "Spearman and Pearson are computed for final_Q and h2 only, against the artifact mean rating. Constant forecasts are skipped. Correlations use equal weight per artifact.",
    "The bootstrap draws whole test tasks. Unique test task ids are sorted lexicographically. Each draw calls rng.integers(0, n_tasks, n_tasks) on numpy.random.default_rng(20261124). Artifacts of a drawn task are included once per time that task is drawn. The statistic is the equal-artifact mean on that multiset. The 95% interval is the NumPy linear 2.5 and 97.5 percentiles. The estimate is the full-sample paired difference.",
    "Ordinal model: P(score<=k)=sigmoid(theta_k-w.x) for k=0..4, with theta_0=alpha_0 and later thresholds separated by softplus(alpha)+1e-12. x is [mean(astra), mean(opus), h3_score, h3_expected], standardised with the train+val mean and population sd (ddof=0). The fit minimises mean per-artifact CE on train+val only, with no penalty and no uniform mixture. Parameters are the best of deterministic L-BFGS-B starts, then Nelder-Mead, then a final L-BFGS-B polish. A different SciPy build can move the fit within optimiser tolerance.",
    "Every reported RPS, CE, and TVD is the equal-weight mean of per-artifact scores. Human P is that artifact's empirical histogram on scores 0..5.",
    "A final_Q row passes the sum check when abs(sum-1) <= 1e-6. The maximum absolute sum error is reported.",
    "The 1e-12 threshold gap keeps theta strictly increasing in float64. It is a constraint, not a penalty on w.",
]


def softplus(x):
    x = np.asarray(x, dtype=float)
    out = np.empty_like(x, dtype=float)
    pos = x > 0.0
    out[pos] = x[pos] + np.log1p(np.exp(-x[pos]))
    out[~pos] = np.log1p(np.exp(x[~pos]))
    return out


def inv_softplus(g):
    g = np.maximum(np.asarray(g, dtype=float), 1e-15)
    capped = np.minimum(g, 20.0)
    return np.where(g > 20.0, g, np.log(np.expm1(capped)))


def theta_from_alpha(alpha):
    alpha = np.asarray(alpha, dtype=float)
    theta = np.empty(5, dtype=float)
    theta[0] = alpha[0]
    theta[1:] = alpha[0] + np.cumsum(softplus(alpha[1:]) + MIN_GAP)
    return theta


def alpha_from_theta(theta):
    theta = np.asarray(theta, dtype=float)
    alpha = np.empty(5, dtype=float)
    alpha[0] = theta[0]
    alpha[1:] = inv_softplus(np.diff(theta) - MIN_GAP)
    return alpha


def expit(z):
    z = np.clip(np.asarray(z, dtype=float), -60.0, 60.0)
    return 1.0 / (1.0 + np.exp(-z))


def floor_renorm(q, eps=EPS):
    q = np.maximum(np.asarray(q, dtype=float), eps)
    return q / q.sum()


def as_score_array(values, name):
    arr = np.asarray(values, dtype=float)
    if arr.size < 1 or not np.all(np.isfinite(arr)):
        raise ValueError(name)
    if np.any(arr < 0) or np.any(arr > 5) or np.any(arr != np.floor(arr)):
        raise ValueError(name)
    return arr.astype(int)


def human_hist(artifact):
    ratings = as_score_array(artifact["ratings"], artifact["id"] + " ratings")
    counts = np.bincount(ratings, minlength=6).astype(float)
    if counts.shape != (6,):
        raise ValueError(artifact["id"] + " ratings")
    return counts / counts.sum()


def pooled_rating_q(artifacts):
    ratings = np.concatenate(
        [as_score_array(a["ratings"], a["id"] + " ratings") for a in artifacts]
    )
    counts = np.bincount(ratings, minlength=6).astype(float)
    if counts.shape != (6,):
        raise ValueError("pooled ratings outside 0..5")
    freq = counts / counts.sum()
    return floor_renorm(freq), int(ratings.size), [int(c) for c in counts]


def h2_q(artifact):
    scores = np.concatenate(
        [
            as_score_array(artifact["astra"], artifact["id"] + " astra"),
            as_score_array(artifact["opus"], artifact["id"] + " opus"),
        ]
    )
    counts = np.bincount(scores, minlength=6).astype(float)
    if counts.shape != (6,):
        raise ValueError(artifact["id"] + " h2")
    freq = counts / float(scores.size)
    return floor_renorm(freq), int(scores.size)


def features_of(artifact):
    astra = as_score_array(artifact["astra"], artifact["id"] + " astra")
    opus = as_score_array(artifact["opus"], artifact["id"] + " opus")
    h3 = float(artifact["h3_score"])
    h3e = float(artifact["h3_expected"])
    if not np.isfinite(h3) or not np.isfinite(h3e):
        raise ValueError(artifact["id"] + " h3")
    return np.array([astra.mean(), opus.mean(), h3, h3e], dtype=float)


def per_artifact_metrics(p, q):
    cp = np.cumsum(p, axis=1)[:, :5]
    cq = np.cumsum(q, axis=1)[:, :5]
    rps = np.mean((cq - cp) ** 2 + cp * (1.0 - cp), axis=1)
    qf = np.maximum(q, EPS)
    qf = qf / qf.sum(axis=1, keepdims=True)
    ce = -np.sum(p * np.log(qf), axis=1)
    tvd = 0.5 * np.sum(np.abs(p - q), axis=1)
    return np.column_stack([rps, ce, tvd])


def corr_pair(human_mean, forecast_q):
    if human_mean.shape[0] < 3:
        return None, None
    fmean = forecast_q @ SCORES
    if float(np.std(human_mean)) == 0.0 or float(np.std(fmean)) == 0.0:
        return None, None
    rho, _ = spearmanr(human_mean, fmean)
    pear, _ = pearsonr(human_mean, fmean)
    rho = float(rho) if np.isfinite(rho) else None
    pear = float(pear) if np.isfinite(pear) else None
    return rho, pear


def summarise(metrics, spearman, pearson):
    return {
        "n": int(metrics.shape[0]),
        "rps": float(metrics[:, 0].mean()),
        "ce": float(metrics[:, 1].mean()),
        "tvd": float(metrics[:, 2].mean()),
        "spearman": spearman,
        "pearson": pearson,
    }


def ordinal_pmf(x, alpha, w):
    theta = theta_from_alpha(alpha)
    eta = x @ np.asarray(w, dtype=float)
    cdf = expit(theta[None, :] - eta[:, None])
    pmf = np.empty((x.shape[0], 6), dtype=float)
    pmf[:, 0] = cdf[:, 0]
    pmf[:, 1:5] = np.diff(cdf, axis=1)
    pmf[:, 5] = 1.0 - cdf[:, 4]
    pmf = np.maximum(pmf, 0.0)
    pmf /= pmf.sum(axis=1, keepdims=True)
    return pmf, theta


def mean_ce(p, q):
    qf = np.maximum(q, EPS)
    qf = qf / qf.sum(axis=1, keepdims=True)
    return float(-np.mean(np.sum(p * np.log(qf), axis=1)))


def validate(data):
    fatal = []
    warnings = []
    ids = [a.get("id") for a in data]
    dup_ids = sorted({i for i in ids if ids.count(i) > 1})
    if dup_ids:
        warnings.append("duplicate artifact ids: " + ", ".join(map(str, dup_ids)))

    split_by_task = defaultdict(set)
    set_by_task = defaultdict(set)
    empty_ratings = []
    bad_ratings = []
    bad_judges = []
    h2_not_six = []
    missing_final = []
    unexpected_final = []
    bad_final = []
    sum_errors = []
    missing_fields = []

    for a in data:
        art_id = str(a.get("id"))
        for key in ("id", "task", "set", "split", "ratings", "astra", "opus", "h3_score", "h3_expected"):
            if key not in a:
                missing_fields.append(art_id + ":" + key)
        if missing_fields:
            continue
        split_by_task[a["task"]].add(a["split"])
        set_by_task[a["task"]].add(a["set"])
        ratings = a["ratings"]
        if len(ratings) < 1:
            empty_ratings.append(art_id)
        else:
            try:
                as_score_array(ratings, art_id)
            except ValueError:
                bad_ratings.append(art_id)
        try:
            n_h2 = len(a["astra"]) + len(a["opus"])
            as_score_array(a["astra"], art_id)
            as_score_array(a["opus"], art_id)
            if n_h2 != 6:
                h2_not_six.append(art_id)
        except ValueError:
            bad_judges.append(art_id)
        if not np.isfinite(float(a["h3_score"])) or not np.isfinite(float(a["h3_expected"])):
            bad_judges.append(art_id + ":h3")
        has_final = "final_Q" in a and a["final_Q"] is not None
        if a["split"] == "test" and not has_final:
            missing_final.append(art_id)
        if a["split"] != "test" and has_final:
            unexpected_final.append(art_id)
        if has_final:
            q = a["final_Q"]
            if len(q) != 6 or not np.all(np.isfinite(q)) or np.any(np.asarray(q, dtype=float) < 0):
                bad_final.append(art_id)
            else:
                sum_errors.append(abs(math.fsum(q) - 1.0))

    if missing_fields:
        fatal.append("missing fields: " + ", ".join(missing_fields[:20]))
    if empty_ratings:
        fatal.append("fewer than 1 rating: " + ", ".join(empty_ratings))
    if bad_ratings:
        fatal.append("ratings outside integer 0..5: " + ", ".join(bad_ratings))
    if bad_judges:
        fatal.append("judge scores unusable: " + ", ".join(bad_judges))
    if missing_final:
        fatal.append("test artifacts missing final_Q: " + ", ".join(missing_final))
    if bad_final:
        fatal.append("final_Q not a nonnegative length-6 finite vector: " + ", ".join(bad_final))
    if h2_not_six:
        warnings.append("astra+opus length is not 6 for " + str(len(h2_not_six)) + " artifacts")
    if unexpected_final:
        warnings.append("final_Q present off the test split: " + ", ".join(unexpected_final))

    multi_split = sorted(t for t, ss in split_by_task.items() if len(ss) > 1)
    multi_set = sorted(t for t, ss in set_by_task.items() if len(ss) > 1)
    max_sum_err = float(max(sum_errors)) if sum_errors else None
    sum_ok = bool(sum_errors) and max_sum_err <= EPS and not bad_final and not missing_final

    observed_splits = []
    for name in ("train", "val", "test"):
        if any(a.get("split") == name for a in data):
            observed_splits.append(name)
    for name in sorted({a.get("split") for a in data} - set(observed_splits)):
        observed_splits.append(name)
    observed_sets = [name for name in ("old", "new") if any(a.get("set") == name for a in data)]
    for name in sorted({a.get("set") for a in data} - set(observed_sets)):
        observed_sets.append(name)

    counts = {}
    for split in observed_splits:
        counts[split] = {}
        in_split = [a for a in data if a.get("split") == split]
        for set_name in observed_sets:
            arts = [a for a in in_split if a.get("set") == set_name]
            counts[split][set_name] = {
                "artifacts": len(arts),
                "tasks": len({a["task"] for a in arts}),
            }
        counts[split]["all"] = {
            "artifacts": len(in_split),
            "tasks": len({a["task"] for a in in_split}),
        }

    n_test = counts.get("test", {}).get("all", {}).get("artifacts", 0)
    checks = {
        "no_task_in_multiple_splits": len(multi_split) == 0,
        "no_artifact_with_fewer_than_one_rating": len(empty_ratings) == 0,
        "final_Q_sums_to_one": bool(sum_ok),
        "final_Q_present_exactly_on_test": len(missing_final) == 0 and len(unexpected_final) == 0,
        "n_artifacts_is_175": len(data) == 175,
        "n_test_artifacts_is_70": n_test == 70,
    }
    report = {
        "n_artifacts": len(data),
        "n_tasks": len({a.get("task") for a in data}),
        "counts_by_split_and_set": counts,
        "checks": checks,
        "tasks_in_multiple_splits": multi_split,
        "tasks_in_multiple_sets": multi_set,
        "artifacts_with_fewer_than_one_rating": empty_ratings,
        "n_final_Q": len(sum_errors),
        "max_abs_final_Q_sum_error": max_sum_err,
        "final_Q_sum_tolerance": EPS,
        "duplicate_artifact_ids": dup_ids,
        "fatal": fatal,
        "warnings": warnings,
    }
    return report


def fit_ordinal(x_tv, p_tv):
    y = p_tv @ SCORES
    y = y - y.mean()
    w_ols, *_ = np.linalg.lstsq(x_tv, y, rcond=None)
    cp = np.cumsum(p_tv.mean(axis=0))[:5]
    cp = np.clip(cp, 0.05, 0.95)
    theta0 = np.log(cp) - np.log(1.0 - cp)
    for k in range(1, 5):
        if theta0[k] <= theta0[k - 1] + 1e-3:
            theta0[k] = theta0[k - 1] + 1e-3

    starts = [np.zeros(9, dtype=float)]
    for scale in (0.5, 1.0, 2.0):
        alpha_s = alpha_from_theta(theta0 * scale)
        for w in (np.zeros(4), w_ols, 0.5 * w_ols, 2.0 * w_ols, -w_ols):
            starts.append(np.concatenate([alpha_s, np.asarray(w, dtype=float)]))

    def loss(params):
        pmf, _ = ordinal_pmf(x_tv, params[:5], params[5:])
        if not np.all(np.isfinite(pmf)):
            return 1e6
        value = mean_ce(p_tv, pmf)
        if not np.isfinite(value):
            return 1e6
        return value

    lbfgs = {"maxiter": 1000, "ftol": 1e-14, "gtol": 1e-9, "disp": False}
    best_x = None
    best_f = np.inf
    for start in starts:
        res = minimize(loss, start, method="L-BFGS-B", options=lbfgs)
        if np.isfinite(res.fun) and float(res.fun) < best_f:
            best_f = float(res.fun)
            best_x = np.asarray(res.x, dtype=float)
    nelder = minimize(
        loss,
        best_x,
        method="Nelder-Mead",
        options={"maxiter": 20000, "xatol": 1e-12, "fatol": 1e-14},
    )
    if np.isfinite(nelder.fun) and float(nelder.fun) < best_f:
        best_f = float(nelder.fun)
        best_x = np.asarray(nelder.x, dtype=float)
    final = minimize(loss, best_x, method="L-BFGS-B", options=lbfgs)
    if np.isfinite(final.fun) and float(final.fun) < best_f:
        best_f = float(final.fun)
        best_x = np.asarray(final.x, dtype=float)
    return best_x, best_f, len(starts)


def percentile_ci(samples):
    try:
        lohi = np.percentile(samples, [2.5, 97.5], axis=0, method="linear")
    except TypeError:
        lohi = np.percentile(samples, [2.5, 97.5], axis=0)
    return lohi


def task_bootstrap(test_artifacts, stack):
    tasks = sorted({a["task"] for a in test_artifacts})
    groups = []
    for task in tasks:
        ix = [i for i, a in enumerate(test_artifacts) if a["task"] == task]
        groups.append(np.asarray(ix, dtype=int))
    n_tasks = len(tasks)
    task_sum = np.zeros((n_tasks, 3, 3), dtype=float)
    task_n = np.zeros(n_tasks, dtype=float)
    for i, ix in enumerate(groups):
        task_sum[i] = stack[ix].sum(axis=0)
        task_n[i] = float(ix.size)
    recon = task_sum.sum(axis=0) / task_n.sum()
    ref = np.stack([stack[:, j, :].mean(axis=0) for j in range(3)], axis=0)
    if not np.allclose(recon, ref, rtol=1e-10, atol=1e-10):
        raise RuntimeError("task aggregation does not reproduce the artifact mean")

    rng = np.random.default_rng(BOOT_SEED)
    diff_const = np.empty((N_BOOT, 3), dtype=float)
    diff_h2 = np.empty((N_BOOT, 3), dtype=float)
    for draw_i in range(N_BOOT):
        draw = rng.integers(0, n_tasks, n_tasks)
        means = task_sum[draw].sum(axis=0) / task_n[draw].sum()
        diff_const[draw_i] = means[0] - means[1]
        diff_h2[draw_i] = means[0] - means[2]
    return {
        "tasks_sorted": tasks,
        "artifacts_per_task": {t: int(groups[i].size) for i, t in enumerate(tasks)},
        "diff_const": diff_const,
        "diff_h2": diff_h2,
    }


def contrast_block(estimate, samples):
    lohi = percentile_ci(samples)
    block = {}
    for j, name in enumerate(METRIC_NAMES):
        lo = float(lohi[0, j])
        hi = float(lohi[1, j])
        block[name] = {
            "estimate": float(estimate[j]),
            "ci95": [lo, hi],
            "bootstrap_mean": float(samples[:, j].mean()),
            "fraction_draws_negative": float(np.mean(samples[:, j] < 0.0)),
            "ci_excludes_zero": bool(hi < 0.0 or lo > 0.0),
        }
    return block


def fmt(value):
    if value is None:
        return f"{'skip':>10}"
    return f"{value:10.6f}"


def print_report(out):
    leak = out["task3_leakage_and_counts"]
    print("counts artifacts/tasks")
    counts = leak["counts_by_split_and_set"]
    for split, by_set in counts.items():
        bits = []
        for set_name, rec in by_set.items():
            bits.append(f"{set_name}={rec['artifacts']}/{rec['tasks']}")
        print(f"  {split}: " + "  ".join(bits))
    print(
        f"checks multi_split_ok={leak['checks']['no_task_in_multiple_splits']}"
        f" ratings_ok={leak['checks']['no_artifact_with_fewer_than_one_rating']}"
        f" final_Q_sum_ok={leak['checks']['final_Q_sums_to_one']}"
        f" final_Q_placement_ok={leak['checks']['final_Q_present_exactly_on_test']}"
        f" n175={leak['checks']['n_artifacts_is_175']}"
        f" ntest70={leak['checks']['n_test_artifacts_is_70']}"
        f" max_abs_sum_err={leak['max_abs_final_Q_sum_error']:.3e}"
    )
    if leak["tasks_in_multiple_splits"]:
        print("tasks in multiple splits: " + ", ".join(map(str, leak["tasks_in_multiple_splits"])))
    if leak["warnings"]:
        for line in leak["warnings"]:
            print("warning: " + line)

    print("\nsubset forecast n RPS CE TVD Spearman Pearson")
    for subset, block in out["task1_forecast_metrics"].items():
        print(f"{subset}: n_artifacts={block['n_artifacts']} n_tasks={block['n_tasks']}")
        for name in FORECAST_NAMES:
            row = block["forecasts"][name]
            print(
                f"  {name:<18} {row['n']:4d} {row['rps']:10.6f} {row['ce']:10.6f} "
                f"{row['tvd']:10.6f} {fmt(row['spearman'])} {fmt(row['pearson'])}"
            )

    boot = out["task2_task_bootstrap"]
    print(
        f"\nbootstrap draws={boot['n_draws']} seed={boot['seed']} "
        f"n_tasks={boot['n_tasks']} n_artifacts={boot['n_artifacts']}"
    )
    print(f"{'contrast':<32} {'metric':<6} {'estimate':>10} {'ci2.5':>10} {'ci97.5':>10}")
    for contrast, block in (
        ("final_Q - constant_per_set", boot["final_Q_minus_constant_per_set"]),
        ("final_Q - h2", boot["final_Q_minus_h2"]),
    ):
        for name in METRIC_NAMES:
            rec = block[name]
            print(
                f"{contrast:<32} {name:<6} {rec['estimate']:10.6f} "
                f"{rec['ci95'][0]:10.6f} {rec['ci95'][1]:10.6f}"
            )

    ordinal = out["task4_ordinal_refit"]
    te = ordinal["test_pooled"]
    fin = ordinal["final_Q_test_pooled"]
    delta = ordinal["ordinal_minus_final_Q"]
    print(
        f"\nordinal test RPS={te['rps']:.6f} CE={te['ce']:.6f} TVD={te['tvd']:.6f} "
        f"train_val_CE={ordinal['train_val_mean_ce']:.6f}"
    )
    print(
        f"final_Q test RPS={fin['rps']:.6f} CE={fin['ce']:.6f} TVD={fin['tvd']:.6f}"
    )
    print(
        "ordinal - final_Q "
        f"RPS={delta['rps']:.6f} CE={delta['ce']:.6f} TVD={delta['tvd']:.6f}"
    )
    theta = " ".join(f"{v:.4f}" for v in ordinal["theta"])
    weight = " ".join(f"{v:.4f}" for v in ordinal["w"])
    print(f"theta [{theta}]")
    print(f"w [{weight}] strictly_increasing={ordinal['thresholds_strictly_increasing']}")
    print("\nlimitations")
    for i, line in enumerate(out["limitations"], start=1):
        print(f"{i}. {line}")


def main():
    with open(IN_PATH, encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, list):
        raise SystemExit("qa_input.json must be a list of artifacts")

    leakage = validate(data)
    out = {
        "task3_leakage_and_counts": leakage,
        "limitations": LIMITATIONS,
    }
    if leakage["fatal"]:
        text = json.dumps(out, indent=2, allow_nan=False)
        with open(OUT_PATH, "w", encoding="utf-8") as handle:
            handle.write(text + "\n")
        print_report(out)
        raise SystemExit(1)

    test_artifacts = [a for a in data if a["split"] == "test"]
    tv_artifacts = [a for a in data if a["split"] in ("train", "val")]
    p_test = np.vstack([human_hist(a) for a in test_artifacts])
    human_mean = p_test @ SCORES
    q_final = np.vstack([np.asarray(a["final_Q"], dtype=float) for a in test_artifacts])

    q_by_set = {}
    const_meta = {}
    for set_name in sorted({a["set"] for a in test_artifacts}):
        pool = [a for a in tv_artifacts if a["set"] == set_name]
        if not pool:
            raise SystemExit("no train+val artifacts for set " + str(set_name))
        q_set, n_ratings, counts = pooled_rating_q(pool)
        q_by_set[set_name] = q_set
        const_meta[set_name] = {"n_ratings": n_ratings, "raw_counts": counts, "q": q_set.tolist()}
    q_const = np.vstack([q_by_set[a["set"]] for a in test_artifacts])
    q_pool, n_pool, counts_pool = pooled_rating_q(tv_artifacts)
    q_pool_rows = np.repeat(q_pool[None, :], len(test_artifacts), axis=0)
    q_uniform = np.repeat(np.full(6, 1.0 / 6.0)[None, :], len(test_artifacts), axis=0)
    h2_rows = []
    h2_lengths = []
    for artifact in test_artifacts:
        q_h2, n_scores = h2_q(artifact)
        h2_rows.append(q_h2)
        h2_lengths.append(n_scores)
    q_h2 = np.vstack(h2_rows)

    forecast_q = {
        "final_Q": q_final,
        "constant_per_set": q_const,
        "pooled_constant": q_pool_rows,
        "uniform": q_uniform,
        "h2": q_h2,
    }
    subset_masks = {
        "pooled": np.ones(len(test_artifacts), dtype=bool),
        "old": np.asarray([a["set"] == "old" for a in test_artifacts], dtype=bool),
        "new": np.asarray([a["set"] == "new" for a in test_artifacts], dtype=bool),
    }
    task1 = {}
    metric_rows = {}
    for subset, mask in subset_masks.items():
        if not np.any(mask):
            raise SystemExit("empty test subset: " + subset)
        forecasts = {}
        for name in FORECAST_NAMES:
            rows = per_artifact_metrics(p_test[mask], forecast_q[name][mask])
            if name in SKIP_CORR:
                spearman, pearson = None, None
            else:
                spearman, pearson = corr_pair(human_mean[mask], forecast_q[name][mask])
            forecasts[name] = summarise(rows, spearman, pearson)
            if subset == "pooled":
                metric_rows[name] = per_artifact_metrics(p_test, forecast_q[name])
        task_ids = {a["task"] for a, keep in zip(test_artifacts, mask) if keep}
        task1[subset] = {
            "n_artifacts": int(mask.sum()),
            "n_tasks": len(task_ids),
            "forecasts": forecasts,
        }

    x_tv = np.vstack([features_of(a) for a in tv_artifacts])
    p_tv = np.vstack([human_hist(a) for a in tv_artifacts])
    x_mean = x_tv.mean(axis=0)
    x_sd = x_tv.std(axis=0, ddof=0)
    x_sd_used = np.where(x_sd == 0.0, 1.0, x_sd)
    x_tv_s = (x_tv - x_mean) / x_sd_used
    x_te = np.vstack([features_of(a) for a in test_artifacts])
    x_te_s = (x_te - x_mean) / x_sd_used
    params, train_ce, n_starts = fit_ordinal(x_tv_s, p_tv)
    alpha, weight = params[:5], params[5:]
    q_ord, theta = ordinal_pmf(x_te_s, alpha, weight)
    ord_metrics = per_artifact_metrics(p_test, q_ord)
    ordinal_summary = summarise(ord_metrics, *corr_pair(human_mean, q_ord))
    final_summary = task1["pooled"]["forecasts"]["final_Q"]
    ordinal = {
        "x_features": ["mean_astra", "mean_opus", "h3_score", "h3_expected"],
        "standardise": "train+val artifact mean and population sd (ddof=0), applied to test",
        "x_mean": [float(v) for v in x_mean],
        "x_sd": [float(v) for v in x_sd],
        "zero_sd_replaced": [bool(v) for v in (x_sd == 0.0)],
        "theta": [float(v) for v in theta],
        "w": [float(v) for v in weight],
        "thresholds_strictly_increasing": bool(np.all(np.diff(theta) > 0.0)),
        "min_theta_gap": float(np.diff(theta).min()),
        "train_val_n_artifacts": len(tv_artifacts),
        "train_val_mean_ce": float(train_ce),
        "n_optimiser_starts": int(n_starts),
        "test_pooled": {
            "n": ordinal_summary["n"],
            "rps": ordinal_summary["rps"],
            "ce": ordinal_summary["ce"],
            "tvd": ordinal_summary["tvd"],
            "spearman": ordinal_summary["spearman"],
            "pearson": ordinal_summary["pearson"],
        },
        "final_Q_test_pooled": {
            "n": final_summary["n"],
            "rps": final_summary["rps"],
            "ce": final_summary["ce"],
            "tvd": final_summary["tvd"],
        },
        "ordinal_minus_final_Q": {
            "rps": float(ordinal_summary["rps"] - final_summary["rps"]),
            "ce": float(ordinal_summary["ce"] - final_summary["ce"]),
            "tvd": float(ordinal_summary["tvd"] - final_summary["tvd"]),
        },
    }

    stack = np.stack(
        [metric_rows["final_Q"], metric_rows["constant_per_set"], metric_rows["h2"]],
        axis=1,
    )
    boot = task_bootstrap(test_artifacts, stack)
    full_const = np.array(
        [final_summary[name] - task1["pooled"]["forecasts"]["constant_per_set"][name] for name in METRIC_NAMES]
    )
    full_h2 = np.array(
        [final_summary[name] - task1["pooled"]["forecasts"]["h2"][name] for name in METRIC_NAMES]
    )
    sizes = list(boot["artifacts_per_task"].values())
    task2 = {
        "n_draws": N_BOOT,
        "seed": BOOT_SEED,
        "rng": "numpy.random.default_rng",
        "draw": "rng.integers(0, n_tasks, n_tasks)",
        "population": "sorted unique test task ids",
        "n_tasks": len(boot["tasks_sorted"]),
        "n_artifacts": len(test_artifacts),
        "artifacts_per_task_min": int(min(sizes)),
        "artifacts_per_task_max": int(max(sizes)),
        "sorted_test_tasks": boot["tasks_sorted"],
        "artifacts_per_task": boot["artifacts_per_task"],
        "final_Q_minus_constant_per_set": contrast_block(full_const, boot["diff_const"]),
        "final_Q_minus_h2": contrast_block(full_h2, boot["diff_h2"]),
    }

    out = {
        "task1_forecast_metrics": task1,
        "task1_constant_definitions": {
            "weighting": "equal weight per individual train+val rating",
            "per_set": const_meta,
            "pooled": {
                "n_ratings": n_pool,
                "raw_counts": counts_pool,
                "q": q_pool.tolist(),
            },
            "uniform_q": [1.0 / 6.0] * 6,
            "h2_score_counts": {
                "min": int(min(h2_lengths)),
                "max": int(max(h2_lengths)),
            },
        },
        "task2_task_bootstrap": task2,
        "task3_leakage_and_counts": leakage,
        "task4_ordinal_refit": ordinal,
        "limitations": LIMITATIONS,
    }
    text = json.dumps(out, indent=2, allow_nan=False)
    with open(OUT_PATH, "w", encoding="utf-8") as handle:
        handle.write(text + "\n")
    print_report(out)
    print(f"\nwrote {OUT_PATH}")


if __name__ == "__main__":
    main()
