#!/usr/bin/env python3
import json
import math
from pathlib import Path

import numpy as np

FLOOR = 1e-6
SEED = 1
BOOTSTRAP_DRAWS = 2000
SPLIT_DRAWS = 200
JUDGES = ("astra", "opus")
GROUPS = ("old", "new", "pooled")


def validate_scores(values, label, expected_length=None):
    if not isinstance(values, list) or not values:
        raise ValueError(f"{label} must be a nonempty list.")
    if expected_length is not None and len(values) != expected_length:
        raise ValueError(f"{label} must contain {expected_length} scores.")
    if any(type(x) is not int or not 0 <= x <= 5 for x in values):
        raise ValueError(f"{label} must contain integers from 0 through 5.")
    return np.asarray(values, dtype=np.int64)


def smooth_histogram(counts):
    counts = np.asarray(counts, dtype=np.float64)
    total = counts.sum()
    if total <= 0:
        raise ValueError("Cannot construct a distribution from zero ratings.")
    q = np.maximum(counts / total, FLOOR)
    return q / q.sum()


def rps(p, q):
    cp = np.cumsum(p, axis=-1)[..., :5]
    cq = np.cumsum(q, axis=-1)[..., :5]
    return np.mean((cq - cp) ** 2 + cp * (1.0 - cp), axis=-1)


def average_ranks(values):
    values = np.asarray(values, dtype=np.float64)
    order = np.argsort(values, kind="mergesort")
    sorted_values = values[order]
    ranks = np.empty(len(values), dtype=np.float64)
    start = 0
    while start < len(values):
        end = start + 1
        while end < len(values) and sorted_values[end] == sorted_values[start]:
            end += 1
        ranks[order[start:end]] = (start + 1 + end) / 2.0
        start = end
    return ranks


def correlation(x, y):
    x = np.asarray(x, dtype=np.float64)
    y = np.asarray(y, dtype=np.float64)
    if len(x) < 2:
        return None
    xc = x - x.mean()
    yc = y - y.mean()
    denominator = np.linalg.norm(xc) * np.linalg.norm(yc)
    if denominator == 0.0:
        return None
    return float(np.clip(np.dot(xc, yc) / denominator, -1.0, 1.0))


def mean_or_none(values):
    return float(np.mean(values)) if len(values) else None


def main():
    artifacts = json.loads(Path("qa_input.json").read_text(encoding="utf-8"))
    if not isinstance(artifacts, list) or len(artifacts) != 175:
        raise ValueError("qa_input.json must contain a list of 175 artifacts.")

    ratings = []
    sets = []
    tasks = []
    judge_scores = {judge: [] for judge in JUDGES}

    for i, artifact in enumerate(artifacts):
        if not isinstance(artifact, dict):
            raise ValueError(f"Artifact {i} must be an object.")
        required = {"set", "id", "task", "ratings", "astra", "opus"}
        missing = required.difference(artifact)
        if missing:
            raise ValueError(f"Artifact {i} is missing fields: {sorted(missing)}")
        if artifact["set"] not in ("old", "new"):
            raise ValueError(f"Artifact {i} has an invalid set.")
        task = artifact["task"]
        if type(task) not in (str, int):
            raise ValueError(f"Artifact {i}: task must be a string or integer.")

        sets.append(artifact["set"])
        # Preserve the distinction between integer and string identifiers.
        tasks.append((type(task).__name__, task))
        ratings.append(validate_scores(artifact["ratings"], f"Artifact {i} ratings"))
        for judge in JUDGES:
            judge_scores[judge].append(
                validate_scores(artifact[judge], f"Artifact {i} {judge}", 3)
            )

    if sets.count("old") != 75 or sets.count("new") != 100:
        raise ValueError("Expected exactly 75 old artifacts and 100 new artifacts.")

    n = len(artifacts)
    sets = np.asarray(sets)
    indices = {
        "old": np.flatnonzero(sets == "old"),
        "new": np.flatnonzero(sets == "new"),
        "pooled": np.arange(n),
    }
    counts = np.stack([np.bincount(x, minlength=6) for x in ratings])
    p = counts / counts.sum(axis=1, keepdims=True)
    human_means = p @ np.arange(6, dtype=np.float64)

    warnings = [
        "The split-half request does not specify a direction for its asymmetric "
        "RPS definition. This script reports the average of both directions, "
        "using unsmoothed empirical half histograms. Odd rating counts produce "
        "halves of floor(m/2) and ceil(m/2)."
    ]

    def constant_losses(pool_indices):
        total = counts[pool_indices].sum(axis=0)
        task_totals = {}
        for i in pool_indices:
            task = tasks[i]
            if task not in task_totals:
                task_totals[task] = np.zeros(6, dtype=np.int64)
            task_totals[task] += counts[i]

        distributions = {}
        for task, task_total in task_totals.items():
            remaining = total - task_total
            distributions[task] = (
                smooth_histogram(remaining) if remaining.sum() > 0 else None
            )

        losses = np.full(len(pool_indices), np.nan, dtype=np.float64)
        for position, i in enumerate(pool_indices):
            q = distributions[tasks[i]]
            if q is not None:
                losses[position] = rps(p[i], q)
        return losses

    within_set_losses = np.full(n, np.nan, dtype=np.float64)
    for group in ("old", "new"):
        within_set_losses[indices[group]] = constant_losses(indices[group])
    pooled_constant_losses = constant_losses(indices["pooled"])

    def baseline_mean(values, label):
        if not np.all(np.isfinite(values)):
            warnings.append(
                f"{label} is undefined: at least one artifact has no ratings "
                "from other tasks in the required baseline pool. No artifacts "
                "were silently omitted; the reported baseline is null."
            )
            return None
        return float(np.mean(values))

    constant_results = {
        group: {
            "set_aware_rps": baseline_mean(
                within_set_losses[indices[group]], f"{group} set-aware constant"
            )
        }
        for group in GROUPS
    }
    constant_results["pooled"]["pooled_rps"] = baseline_mean(
        pooled_constant_losses, "pooled constant"
    )

    losses = {}
    q_by_judge = {}
    means_by_judge = {}
    for judge in JUDGES:
        scores = np.stack(judge_scores[judge])
        q = np.stack(
            [smooth_histogram(np.bincount(x, minlength=6)) for x in scores]
        )
        q_by_judge[judge] = q
        means_by_judge[judge] = scores.mean(axis=1)
        losses[judge] = rps(p, q)

    # Task bootstrap: every sampled task contributes all of its artifacts,
    # including multiplicities; each draw is an artifact-weighted mean.
    new_tasks = {}
    for i in indices["new"]:
        new_tasks.setdefault(tasks[i], []).append(i)
    task_members = list(new_tasks.values())
    task_sizes = np.asarray([len(x) for x in task_members], dtype=np.float64)
    task_sums = np.asarray(
        [[losses[judge][members].sum() for judge in JUDGES]
         for members in task_members],
        dtype=np.float64,
    )
    bootstrap_rng = np.random.default_rng(SEED)
    bootstrap_values = np.empty((BOOTSTRAP_DRAWS, len(JUDGES)))
    for draw in range(BOOTSTRAP_DRAWS):
        sampled = bootstrap_rng.integers(
            0, len(task_members), size=len(task_members)
        )
        bootstrap_values[draw] = (
            task_sums[sampled].sum(axis=0) / task_sizes[sampled].sum()
        )
    intervals = {
        judge: np.percentile(bootstrap_values[:, j], [2.5, 97.5]).tolist()
        for j, judge in enumerate(JUDGES)
    }
    if len(task_members) == 1:
        warnings.append(
            "The new set has only one task; its task-bootstrap interval is "
            "degenerate and cannot describe variation across tasks."
        )

    # Independent random stream; the split-half check is human-only and
    # therefore identical for both judges.
    split_rng = np.random.default_rng(SEED)
    split_losses = np.full(n, np.nan, dtype=np.float64)
    for i, values in enumerate(ratings):
        if len(values) < 2:
            continue
        split_at = len(values) // 2
        accumulated = 0.0
        for _ in range(SPLIT_DRAWS):
            shuffled = split_rng.permutation(values)
            half_a = np.bincount(shuffled[:split_at], minlength=6) / split_at
            half_b = (
                np.bincount(shuffled[split_at:], minlength=6)
                / (len(values) - split_at)
            )
            accumulated += 0.5 * (
                float(rps(half_a, half_b)) + float(rps(half_b, half_a))
            )
        split_losses[i] = accumulated / SPLIT_DRAWS

    split_results = {}
    for group in GROUPS:
        eligible = indices[group][np.isfinite(split_losses[indices[group]])]
        split_results[group] = {
            "n_artifacts": int(len(eligible)),
            "rps": mean_or_none(split_losses[eligible]),
        }
        if not len(eligible):
            warnings.append(
                f"{group} split-half RPS is undefined: no artifact has "
                "at least two human ratings."
            )

    rows = []
    for judge in JUDGES:
        for group in GROUPS:
            ix = indices[group]
            q = q_by_judge[judge][ix]
            judge_means = means_by_judge[judge][ix]
            human = human_means[ix]
            pearson = correlation(judge_means, human)
            spearman = correlation(average_ranks(judge_means), average_ranks(human))
            if pearson is None or spearman is None:
                warnings.append(
                    f"{judge}/{group}: correlation is undefined because "
                    "a variable is constant or fewer than two artifacts exist."
                )

            rows.append({
                "judge": judge,
                "set": group,
                "n": int(len(ix)),
                "rps": float(losses[judge][ix].mean()),
                "ce": float((-np.sum(p[ix] * np.log(q), axis=1)).mean()),
                "tvd": float((0.5 * np.abs(p[ix] - q).sum(axis=1)).mean()),
                "spearman": spearman,
                "pearson": pearson,
                "constant_rps": dict(constant_results[group]),
                "new_set_rps_95_percentile_task_bootstrap_interval":
                    intervals[judge] if group == "new" else None,
                "split_half": dict(split_results[group]),
            })

    result = {
        "metadata": {
            "input": "qa_input.json",
            "artifact_weighting": "Equal weight per artifact.",
            "judge_smoothing": "Normalize histogram, floor bins at 1e-6, renormalize.",
            "correlation_scores": "Raw judge mean versus raw human mean.",
            "rps_thresholds": [0, 1, 2, 3, 4],
            "rps_definition": "mean((CQ-CP)^2 + CP*(1-CP))",
            "ce_log_base": "e",
            "baseline_pooling": "Pool individual human ratings, not artifact histograms.",
            "baseline_task_exclusion":
                "Exclude the artifact's entire task within the specified pool; "
                "pooled baselines exclude matching tasks across both sets.",
            "bootstrap": {
                "set": "new",
                "unit": "task",
                "n_tasks": len(task_members),
                "draws": BOOTSTRAP_DRAWS,
                "seed": SEED,
                "rng": "numpy.random.default_rng (PCG64)",
                "percentiles": [2.5, 97.5],
                "percentile_interpolation": "linear",
                "shared_task_draws_across_judges": True,
            },
            "split_half": {
                "draws_per_eligible_artifact": SPLIT_DRAWS,
                "seed": SEED,
                "rng": "Independent numpy.random.default_rng (PCG64)",
                "minimum_ratings": 2,
                "half_sizes": "floor(m/2), ceil(m/2)",
                "smoothing": None,
                "definition": "0.5 * (RPS(P_half_a,Q_half_b) + RPS(P_half_b,Q_half_a))",
                "aggregation": "Average splits within each artifact, then average artifacts.",
                "human_only": True,
            },
            "undefined_values": "JSON null; printed as NA.",
        },
        "results": rows,
        "uncertainties_and_warnings": warnings,
    }
    Path("qa_result.json").write_text(
        json.dumps(result, indent=2, allow_nan=False) + "\n",
        encoding="utf-8",
    )

    def fmt(value):
        return "NA" if value is None else f"{value:.6f}"

    print(
        f"{'Judge':<6} {'Set':<6} {'n':>3} {'RPS':>9} {'CE':>9} {'TVD':>9} "
        f"{'Spear':>9} {'Pearson':>9} {'C-set':>9} {'C-pool':>9} "
        f"{'New RPS 95% CI':>21} {'Split':>9} {'nSplit':>6}"
    )
    for row in rows:
        interval = row["new_set_rps_95_percentile_task_bootstrap_interval"]
        ci = "-" if interval is None else f"[{interval[0]:.6f},{interval[1]:.6f}]"
        constant = row["constant_rps"]
        pooled_text = fmt(constant["pooled_rps"]) if "pooled_rps" in constant else "-"
        print(
            f"{row['judge']:<6} {row['set']:<6} {row['n']:>3} "
            f"{fmt(row['rps']):>9} {fmt(row['ce']):>9} {fmt(row['tvd']):>9} "
            f"{fmt(row['spearman']):>9} {fmt(row['pearson']):>9} "
            f"{fmt(constant['set_aware_rps']):>9} {pooled_text:>9} "
            f"{ci:>21} {fmt(row['split_half']['rps']):>9} "
            f"{row['split_half']['n_artifacts']:>6}"
        )
    print("C-set: set-aware constant; C-pool: pooled constant. Saved qa_result.json.")
    for warning in warnings:
        print("Note:", warning)


if __name__ == "__main__":
    main()
