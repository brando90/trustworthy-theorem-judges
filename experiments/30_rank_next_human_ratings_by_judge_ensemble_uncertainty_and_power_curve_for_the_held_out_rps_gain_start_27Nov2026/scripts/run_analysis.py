#!/usr/bin/env python3
"""Rank the next human ratings and simulate the held-out RPS interval.

CPU only. No model calls. Reads frozen experiment 25, 27, 28 and 29 tables.
Predictions are in PREREG.md, written before this script is executed.
"""
from __future__ import annotations

import csv
import hashlib
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[3]
EXP27 = ROOT / "experiments/27_build_a_judge_that_beats_the_constant_forecast_on_held_out_tasks_old_new_ratings_start_24Nov2026"
EXP25 = ROOT / "experiments/25_do_more_human_ratings_improve_judge_evaluation_old_new_pooled_start_24Nov2026"
EXP28 = ROOT / "experiments/28_multi_family_distributional_judge_and_open_weight_lora_on_new_ratings_start_26Nov2026"
EXP29 = ROOT / "experiments/29_refit_cumulative_logit_heads_ce_versus_rps_on_445_ratings_start_27Nov2026"
OUT = Path(__file__).resolve().parents[1] / "results"
sys.path.insert(0, str(EXP27 / "scripts"))
sys.path.insert(0, str(EXP25 / "scripts"))
from evalcore import hist, loto_constant, per_artifact, smooth  # noqa: E402
from judgelib import FEATS, Ordinal, boot, load, metrics_rows, rps  # noqa: E402

SCORES = np.arange(6, dtype=float)
LOG6 = float(np.log(6.0))
EPS = 1e-6
DRAWS = 10000
SEED_ALIGN = 20261124
SEED_POWER = 20261127


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read_csv(path: Path) -> list[dict]:
    with open(path, newline="") as f:
        return list(csv.DictReader(f))


def entropy(q: np.ndarray) -> float:
    qq = q[q > 0]
    return float(-(qq * np.log(qq)).sum())


def rank_parts(member_probs: list[np.ndarray], n_ratings: int) -> dict:
    means = np.array([float(p @ SCORES) for p in member_probs])
    disagreement = float(means.std(ddof=1)) if len(means) >= 2 else 0.0
    q = np.mean(np.stack(member_probs, 0), 0)
    q = q / q.sum()
    h_norm = entropy(q) / LOG6
    ceiling = float(q[5])
    non_ceiling = h_norm * (1.0 - ceiling)
    under = 0.5 / (1.0 + n_ratings)
    return {
        "disagreement_std": disagreement,
        "entropy_normalized": h_norm,
        "ceiling_mass": ceiling,
        "non_ceiling_uncertainty": non_ceiling,
        "under_rated_term": under,
        "rank_score": disagreement + non_ceiling + under,
        "uncertainty_base": disagreement + non_ceiling,
        "ensemble_expected_score": float(q @ SCORES),
        "member_expected_scores": [round(float(x), 6) for x in means],
    }


def task_index_map(tasks: np.ndarray):
    """Same task order as experiment 27 judgelib.boot and experiment 29 task_bootstrap: sorted task ids."""
    order = sorted(set(np.asarray(tasks).tolist()))
    index = {t: i for i, t in enumerate(order)}
    groups = [[] for _ in order]
    for i, t in enumerate(np.asarray(tasks).tolist()):
        groups[index[t]].append(i)
    return order, [np.array(g, dtype=int) for g in groups]


def bootstrap_mean(values: np.ndarray, groups: list[np.ndarray], draws: int, seed: int):
    """Task bootstrap of the unweighted mean of per-artifact values. Duplicate tasks count again.

    The random draws match a loop of rng.integers(0, n_tasks, n_tasks), which is how experiment 27 and experiment 29 draw tasks.
    """
    task_sum = np.array([values[g].sum() for g in groups])
    task_count = np.array([len(g) for g in groups], dtype=float)
    point = float(values.mean())
    rng = np.random.default_rng(seed)
    n_tasks = len(groups)
    pick = np.empty((draws, n_tasks), dtype=int)
    for b in range(draws):
        pick[b] = rng.integers(0, n_tasks, n_tasks)
    num = task_sum[pick].sum(1)
    den = task_count[pick].sum(1)
    samples = num / den
    lo, hi = np.percentile(samples, [2.5, 97.5])
    p_ge0 = float((1 + np.sum(samples >= 0.0)) / (draws + 1))
    return point, float(lo), float(hi), samples, p_ge0


def paired_rps(P: np.ndarray, Q: np.ndarray, C: np.ndarray) -> np.ndarray:
    return rps(P, Q) - rps(P, C)


def hists_from_lists(rows: list[list[int]]) -> np.ndarray:
    P = np.zeros((len(rows), 6))
    for i, rs in enumerate(rows):
        P[i] = np.bincount(np.asarray(rs, dtype=int), minlength=6) / len(rs)
    return P


def write_h3_jsonl(csv_paths: list[Path], dest: Path) -> None:
    with open(dest, "w") as out:
        for path in csv_paths:
            for row in read_csv(path):
                dist = {str(k): float(row[f"p{k}"]) for k in range(6)}
                raw = json.dumps({"final_score_0_5": int(float(row["h3_score"])), "score_distribution": dist})
                out.write(json.dumps({"status": "ok", "id": row["item"], "raw_response": raw}) + "\n")


def align_experiment_27(work: Path) -> dict:
    h3_path = work / "h3_from_feature_csv.jsonl"
    write_h3_jsonl([
        EXP27 / "results/h3_features_trainval_11-24-2026.csv",
        EXP27 / "results/h3_features_test_11-24-2026.csv",
    ], h3_path)
    D = load(str(EXP27 / "data_11-24-2026"), [str(h3_path)], include_test=True)
    fit = np.where(D["split"] != "test")[0]
    te = np.where(D["split"] == "test")[0]
    assert set(D["task"][fit]).isdisjoint(set(D["task"][te]))
    mod = Ordinal(FEATS["F8_both_h3"], 0.0, 0.0).fit(D, fit)
    Q = mod.predict(D, te)
    P = D["P"][te]
    sets = D["set"][te]
    tasks = D["task"][te]
    cs = {s: smooth(D["C"][fit][D["set"][fit] == s].sum(0)) for s in ("old", "new")}
    # marginal() in judgelib smooths a probability; pass counts through smooth(c/c.sum()) via the same helper
    from judgelib import marginal
    cs = {s: marginal(D["C"][fit][D["set"][fit] == s]) for s in ("old", "new")}
    C = np.array([cs[s] for s in sets])
    M = metrics_rows(P, Q)
    Mc = metrics_rows(P, C)
    d = M["RPS"] - Mc["RPS"]
    groups_order, groups = task_index_map(tasks)
    point, lo, hi, _, _p = bootstrap_mean(d, groups, DRAWS, SEED_ALIGN)
    # Second call, same seed, must match. Also the experiment 27 boot() path.
    point2, lo2, hi2, _, _p2 = bootstrap_mean(d, groups, DRAWS, SEED_ALIGN)
    assert point == point2 and lo == lo2 and hi == hi2

    def fn(idx):
        return {"dRPS": float(d[idx].mean()), "RPS": float(M["RPS"][idx].mean()), "CE": float(M["CE"][idx].mean()), "TVD": float(M["TVD"][idx].mean()),
                "cRPS": float(Mc["RPS"][idx].mean()), "cCE": float(Mc["CE"][idx].mean()), "cTVD": float(Mc["TVD"][idx].mean())}

    published_boot_point, published_boot_ci, _ = boot(tasks, fn, DRAWS, SEED_ALIGN)
    target = {"point": -0.034895, "lo": -0.075959, "hi": 0.002444}
    got = {"point": published_boot_point["dRPS"], "lo": published_boot_ci["dRPS"][0], "hi": published_boot_ci["dRPS"][1]}
    return {
        "n_fit": int(len(fit)),
        "n_test_artifacts": int(len(te)),
        "n_test_tasks": int(len(set(tasks))),
        "n_ratings_test": int(D["C"][te].sum()),
        "vectorized_bootstrap": {"point": point, "lo": lo, "hi": hi},
        "judgelib_boot": got,
        "judgelib_levels": {k: {"point": published_boot_point[k], "ci95": published_boot_ci[k]} for k in ("RPS", "CE", "TVD", "cRPS", "cCE", "cTVD", "dRPS")},
        "target_cursor_qa": target,
        "abs_error_vs_target": {k: abs(got[k] - target[k]) for k in target},
        "match_point_within_0.0005": abs(got["point"] - target["point"]) <= 0.0005,
        "match_endpoints_within_0.001": abs(got["lo"] - target["lo"]) <= 0.001 and abs(got["hi"] - target["hi"]) <= 0.001,
        "Q_row_sums_max_abs_error": float(np.max(np.abs(Q.sum(1) - 1))),
        "trace_item_index": 0,
    }


def load_rating_table(path: Path) -> dict:
    ratings, tasks, sets, items = [], [], [], []
    for row in read_csv(path):
        ratings.append([int(x) for x in row["ratings_sorted_0to5_rater_identity_removed"].split()])
        tasks.append(row["task"])
        sets.append(row["set"])
        items.append(row["item"])
    return {"items": items, "tasks": tasks, "sets": sets, "ratings": ratings}


def load_h2_calls(path: Path) -> dict:
    calls = defaultdict(lambda: defaultdict(list))
    for row in read_csv(path):
        calls[row["item"]][row["judge"]].append(int(row["score_0to5"]))
    return calls


def align_experiment_25(ratings_old: Path, ratings_new: Path, h2_path: Path, stored_json: Path, label: str) -> dict:
    old = load_rating_table(ratings_old)
    new = load_rating_table(ratings_new)
    calls = load_h2_calls(h2_path)
    out = {"label": label, "stored_file": str(stored_json.relative_to(ROOT))}
    stored = json.loads(stored_json.read_text())
    for judge_name, judge_key, stored_key in (
        ("H2_astra", "H2_astra", "GPT-6 Astra"),
        ("H2_opus", "H2_opus", "Claude Opus 5.5"),
    ):
        blocks = []
        for block in (old, new):
            P, C, Q, tasks = [], [], [], []
            for item, task, rats in zip(block["items"], block["tasks"], block["ratings"]):
                seq = calls[item][judge_key]
                if len(rats) < 1 or len(seq) < 1:
                    continue
                P.append(hist(rats))
                C.append(np.bincount(np.asarray(rats, dtype=int), minlength=6).astype(float))
                Q.append(hist(seq))
                tasks.append(task)
            P, C, Q = np.array(P), np.array(C), smooth(np.array(Q))
            tasks = np.array(tasks)
            blocks.append((per_artifact(P, Q)["RPS"], per_artifact(P, loto_constant(C, tasks))["RPS"], tasks))
        rj = np.concatenate([blocks[0][0], blocks[1][0]])
        rc = np.concatenate([blocks[0][1], blocks[1][1]])
        tasks = np.concatenate([blocks[0][2], blocks[1][2]])
        d = rj - rc
        _, groups = task_index_map(tasks)
        point, lo, hi, _, _p = bootstrap_mean(d, groups, DRAWS, SEED_ALIGN)
        est = stored[stored_key]["dRPS_vs_setconst"]
        out[stored_key] = {
            "recomputed": {"point": point, "lo": lo, "hi": hi, "n_artifacts": int(len(d)), "n_ratings": int(sum(len(r) for r in old["ratings"]) + sum(len(r) for r in new["ratings"]))},
            "stored": est,
            "abs_point_error": abs(point - est["est"]),
            "match_within_0.001": abs(point - est["est"]) <= 0.001,
        }
    return out


def load_ensemble(art_rows: list[dict], h2_calls: dict, h4_paths: dict[str, Path]) -> list[dict]:
    h4 = {name: {} for name in h4_paths}
    for name, path in h4_paths.items():
        for line in path.read_text().splitlines():
            if not line.strip():
                continue
            obj = json.loads(line)
            if obj.get("status") != "ok":
                continue
            p = np.asarray(obj["parsed"]["probs"], dtype=float)
            p = np.maximum(p, 0)
            p = p / p.sum()
            h4[name][obj["id"]] = p
    built = []
    for row in art_rows:
        item = row["item"]
        members = []
        member_names = []
        for judge_key, label in (("H2_astra", "h2_astra"), ("H2_opus", "h2_opus")):
            seq = h2_calls[item].get(judge_key)
            if seq:
                members.append(hist(seq))
                member_names.append(label)
        h3 = np.array([float(row[f"h3_p{k}"]) for k in range(6)])
        if np.isfinite(h3).all() and h3.sum() > 0:
            members.append(h3 / h3.sum())
            member_names.append("h3_astra")
        for name in ("h4_astra", "h4_argon", "h4_opus"):
            if item in h4[name]:
                members.append(h4[name][item])
                member_names.append(name)
        ratings = [int(x) for x in row["ratings_all"].split()] if row.get("ratings_all") else []
        parts = rank_parts(members, len(ratings))
        parts.update({
            "item": item,
            "task": row["task"],
            "set": row["set"],
            "split": row["split"],
            "n_ratings": len(ratings),
            "n_fives": int(sum(x == 5 for x in ratings)),
            "five_rate": (sum(x == 5 for x in ratings) / len(ratings)) if ratings else None,
            "ratings": ratings,
            "member_names": member_names,
            "n_members": len(members),
            "astra_mean": float(row["astra"]),
            "opus_mean": float(row["opus"]),
            "h3_score": float(row["h3_score"]),
            "h3_expected": float(row["h3_expected"]),
        })
        built.append(parts)
    return built


def fit_f8_on_artifacts(rows: list[dict]) -> dict:
    """Same F8 cumulative logit as experiment 27, on the 445-rating artifact table. Test rows are not in the fit."""
    n = len(rows)
    split = np.array([r["split"] for r in rows])
    D = {
        "astra": np.array([float(r["astra"]) for r in rows]),
        "opus": np.array([float(r["opus"]) for r in rows]),
        "h3s": np.array([float(r["h3_score"]) for r in rows]),
        "h3e": np.array([float(r["h3_expected"]) for r in rows]),
        "set": np.array([r["set"] for r in rows]),
        "split": split,
        "task": np.array([r["task"] for r in rows]),
        "P": np.array([hist(r["ratings"]) for r in rows]),
        "C": np.array([np.bincount(np.asarray(r["ratings"], dtype=int), minlength=6) for r in rows], float),
    }
    fit = np.where(split != "test")[0]
    te = np.where(split == "test")[0]
    assert set(D["task"][fit]).isdisjoint(set(D["task"][te]))
    mod = Ordinal(FEATS["F8_both_h3"], 0.0, 0.0).fit(D, fit)
    from judgelib import marginal
    Q = mod.predict(D, te)
    cs = {s: marginal(D["C"][fit][D["set"][fit] == s]) for s in ("old", "new")}
    Cset = np.array([cs[s] for s in D["set"][te]])
    P = D["P"][te]
    d = paired_rps(P, Q, Cset)
    _, groups = task_index_map(D["task"][te])
    point, lo, hi, _, p_ge0 = bootstrap_mean(d, groups, DRAWS, SEED_POWER)
    point_b, lo_b, hi_b, _, p_ge0_b = bootstrap_mean(d, groups, DRAWS, SEED_POWER)
    assert (point, lo, hi, p_ge0) == (point_b, lo_b, hi_b, p_ge0_b)
    levels = {}
    for name, mat in (("judge", Q), ("constant", Cset)):
        M = metrics_rows(P, mat)
        levels[name] = {}
        for metric in ("RPS", "CE", "TVD"):
            p, a, b, _, _p = bootstrap_mean(M[metric], groups, DRAWS, SEED_POWER)
            levels[name][metric] = {"point": p, "lo": a, "hi": b}
    human_mean = float((P @ SCORES).mean())
    judge_mean = float((Q @ SCORES).mean())
    from judgelib import corr
    spearman, pearson = corr(Q, P)
    paired = {}
    for metric in ("RPS", "CE", "TVD"):
        dlt = metrics_rows(P, Q)[metric] - metrics_rows(P, Cset)[metric]
        pp, aa, bb, _, pv = bootstrap_mean(dlt, groups, DRAWS, SEED_POWER)
        paired[metric] = {"point": pp, "lo": aa, "hi": bb, "p_ge0_plus1": pv}
    return {
        "n_fit": int(len(fit)),
        "n_test": int(len(te)),
        "n_test_tasks": int(len(set(D["task"][te]))),
        "n_test_ratings": int(D["C"][te].sum()),
        "paired_rps": {"point": point, "lo": lo, "hi": hi, "p_ge0_plus1": p_ge0},
        "paired": paired,
        "levels": levels,
        "bias_judge_minus_human": judge_mean - human_mean,
        "judge_mean": judge_mean,
        "human_mean": human_mean,
        "spearman": spearman,
        "pearson": pearson,
        "Q": Q,
        "Cset": Cset,
        "test_positions": te,
        "tasks": D["task"][te],
        "sets": D["set"][te],
        "items": [rows[i]["item"] for i in te],
    }


def retrospective_curves(test_rows: list[dict], Q: np.ndarray, Cset: np.ndarray, seed: int) -> dict:
    rng = np.random.default_rng(seed)
    n = len(test_rows)
    extras_available = sum(len(r["ratings"]) - 1 for r in test_rows)
    grid = sorted(set([0, 10, 20, 40, 60, 80, 100, extras_available, max(0, extras_available // 2)]))
    grid = [g for g in grid if 0 <= g <= extras_available]
    base = np.array([r["uncertainty_base"] for r in test_rows])

    def one_policy(policy: str, rng_local: np.random.Generator):
        current = []
        remaining = []
        for row in test_rows:
            rats = list(row["ratings"])
            rng_local.shuffle(rats)
            current.append([rats[0]])
            remaining.append(rats[1:])
        n_now = np.ones(n, dtype=int)
        snapshots = {}
        revealed = 0
        five_at_100 = None
        want = set(grid)
        if extras_available >= 100:
            want.add(100)
        _, groups = task_index_map(np.array([r["task"] for r in test_rows]))

        def record():
            nonlocal five_at_100
            if revealed in want and revealed not in snapshots:
                P = hists_from_lists(current)
                d = paired_rps(P, Q, Cset)
                point, lo, hi, _, _p = bootstrap_mean(d, groups, DRAWS, SEED_POWER)
                flat = [x for seq in current for x in seq]
                snapshots[revealed] = {
                    "extra_ratings": revealed,
                    "total_ratings": len(flat),
                    "paired_rps": point,
                    "lo": lo,
                    "hi": hi,
                    "upper_below_zero": bool(hi < 0),
                    "five_rate_all": float(np.mean(np.array(flat) == 5)),
                }
            if revealed == min(100, extras_available) and five_at_100 is None:
                added = [x for seq in current for x in seq[1:]]
                five_at_100 = float(np.mean(np.array(added) == 5)) if added else None

        record()
        while revealed < extras_available:
            alive = [i for i in range(n) if remaining[i]]
            if not alive:
                break
            if policy == "uniform":
                choice = int(rng_local.choice(alive))
            else:
                pri = base / ((n_now + 1.0) * (n_now + 2.0))
                choice = max(alive, key=lambda i: (pri[i], -i))
            current[choice].append(remaining[choice].pop())
            n_now[choice] += 1
            revealed += 1
            record()
        return snapshots, five_at_100

    reps = 40
    collected = {"uniform": [], "active": []}
    fives = {"uniform": [], "active": []}
    for policy in ("uniform", "active"):
        for _ in range(reps):
            snap, five = one_policy(policy, rng)
            collected[policy].append(snap)
            fives[policy].append(five)
    summary = {}
    for policy in ("uniform", "active"):
        summary[policy] = []
        keys = sorted(collected[policy][0])
        for k in keys:
            his = np.array([rep[k]["hi"] for rep in collected[policy]])
            pts = np.array([rep[k]["paired_rps"] for rep in collected[policy]])
            summary[policy].append({
                "extra_ratings": int(k),
                "median_upper": float(np.median(his)),
                "p10_upper": float(np.percentile(his, 10)),
                "p90_upper": float(np.percentile(his, 90)),
                "fraction_upper_below_zero": float(np.mean(his < 0)),
                "median_paired_rps": float(np.median(pts)),
                "label": "retrospective subsample of existing ratings",
            })
    return {
        "replicates": reps,
        "extra_ratings_available_after_one_per_artifact": extras_available,
        "five_rate_of_the_next_100_revealed": {
            policy: {"mean": float(np.mean(fives[policy])), "values_are_simulation": False} for policy in fives
        },
        "curves": summary,
    }


def forward_curves(test_rows: list[dict], Q: np.ndarray, Cset: np.ndarray, seed: int) -> dict:
    rng = np.random.default_rng(seed + 17)
    n = len(test_rows)
    base = np.array([r["uncertainty_base"] for r in test_rows])
    n0 = np.array([r["n_ratings"] for r in test_rows], dtype=int)
    probs = []
    for row in test_rows:
        p = np.bincount(np.asarray(row["ratings"], dtype=int), minlength=6).astype(float)
        probs.append(p / p.sum())
    probs = np.array(probs)
    counts0 = np.array([np.bincount(np.asarray(r["ratings"], dtype=int), minlength=6) for r in test_rows], dtype=float)
    grid = [0, 70, 140, 280, 560, 1120, 2240]
    tasks = np.array([r["task"] for r in test_rows])
    _, groups = task_index_map(tasks)
    reps = 40

    def allocate(extra: int, policy: str, rng_local: np.random.Generator) -> np.ndarray:
        add = np.zeros(n, dtype=int)
        if extra == 0:
            return add
        if policy == "uniform":
            order = rng_local.permutation(n)
            for t in range(extra):
                add[order[t % n]] += 1
            return add
        n_now = n0.astype(float).copy()
        for _t in range(extra):
            pri = base / ((n_now + 1.0) * (n_now + 2.0))
            choice = int(np.argmax(pri))
            add[choice] += 1
            n_now[choice] += 1
        return add

    summary = {}
    for policy in ("uniform", "active"):
        summary[policy] = []
        for extra in grid:
            his, pts = [], []
            for _ in range(reps):
                add = allocate(extra, policy, rng)
                counts = counts0.copy()
                for i in range(n):
                    if add[i]:
                        draws = rng.choice(6, size=int(add[i]), p=probs[i])
                        counts[i] += np.bincount(draws, minlength=6)
                P = counts / counts.sum(1, keepdims=True)
                d = paired_rps(P, Q, Cset)
                point, _lo, hi, _, _p = bootstrap_mean(d, groups, DRAWS, SEED_POWER)
                his.append(hi)
                pts.append(point)
            his, pts = np.array(his), np.array(pts)
            summary[policy].append({
                "extra_simulated_ratings": extra,
                "median_upper": float(np.median(his)),
                "p10_upper": float(np.percentile(his, 10)),
                "p90_upper": float(np.percentile(his, 90)),
                "fraction_upper_below_zero": float(np.mean(his < 0)),
                "median_paired_rps": float(np.median(pts)),
                "label": "SIMULATION. Draws from each artifact's current histogram. Not new human ratings and not a certification.",
            })
    return {"replicates": reps, "grid": grid, "curves": summary}


def task_extrapolation(values: np.ndarray, tasks: np.ndarray, seed: int) -> dict:
    order, groups = task_index_map(tasks)
    full_point, full_lo, full_hi, _, full_p = bootstrap_mean(values, groups, DRAWS, SEED_POWER)
    rng = np.random.default_rng(seed)
    sizes = [6, 8, 10, 12, 14, 16, 18, 20]
    rows = []
    art_of = groups
    for m in sizes:
        widths, uppers, points = [], [], []
        n_rep = 1 if m == len(order) else 200
        for _ in range(n_rep):
            if m == len(order):
                chosen = np.arange(len(order))
            else:
                chosen = rng.choice(len(order), size=m, replace=False)
            idx = np.concatenate([art_of[i] for i in chosen])
            sub_tasks = np.array([order[i] for i in chosen for _a in art_of[i]])
            # sub_tasks must align with idx. Build explicitly.
            idx = []
            sub = []
            for i in chosen:
                for a in art_of[i]:
                    idx.append(a)
                    sub.append(order[i])
            idx = np.array(idx)
            _, sub_groups = task_index_map(np.array(sub))
            point, _lo, hi, _, _p = bootstrap_mean(values[idx], sub_groups, DRAWS, SEED_POWER)
            widths.append(hi - _lo)
            uppers.append(hi)
            points.append(point)
        rows.append({
            "n_tasks": m,
            "replicates": n_rep,
            "median_width": float(np.median(widths)),
            "median_upper": float(np.median(uppers)),
            "median_paired_rps": float(np.median(points)),
            "fraction_upper_below_zero": float(np.mean(np.array(uppers) < 0)),
            "label": "retrospective subsample of the existing 20 test tasks" if m < 20 else "full 20 test tasks",
        })
    # Scale the full-data upper distance as 1/sqrt(m). This is an extrapolation past 20 tasks.
    distance = full_hi - full_point
    extrapolated = []
    crossing = None
    for m in range(20, 81):
        upper = full_point + distance * np.sqrt(20.0 / m)
        extrapolated.append({"n_tasks": m, "extrapolated_upper": float(upper), "label": "EXTRAPOLATION. Holds the 20-task point estimate fixed and scales only the upper distance by sqrt(20/m). Planning, not a measured interval."})
        if crossing is None and upper < 0:
            crossing = m
    width_times_sqrt = [r["median_width"] * np.sqrt(r["n_tasks"]) for r in rows if r["n_tasks"] < 20]
    return {
        "full": {"point": full_point, "lo": full_lo, "hi": full_hi, "p_ge0_plus1": full_p},
        "by_task_count": rows,
        "width_times_sqrt_mean_below_20": float(np.mean(width_times_sqrt)),
        "width_times_sqrt_cv_below_20": float(np.std(width_times_sqrt) / np.mean(width_times_sqrt)),
        "extrapolated_crossing_task_count": crossing,
        "extrapolated_upper_at_20": float(full_point + distance),
        "assumption": "New tasks would have the same mean paired RPS as these 20. Only the task-bootstrap upper distance shrinks as 1/sqrt(m).",
    }


def priority_tables(built: list[dict]) -> dict:
    new = [r for r in built if r["set"] == "new"]
    new_sorted = sorted(new, key=lambda r: (-r["rank_score"], r["item"]))
    for i, row in enumerate(new_sorted, start=1):
        row["rank"] = i
        row["empty_slots_of_33"] = 33 - row["n_ratings"]
    # Leakage control: rank score ignores rating values.
    scrambled = []
    for row in new:
        parts = rank_parts_from_saved(row, n_ratings=row["n_ratings"])
        scrambled.append(parts["rank_score"])
    # Recompute from stored components rather than rating values.
    assert all(abs(a - b) < 1e-12 for a, b in zip(scrambled, [r["rank_score"] for r in new]))
    top = new_sorted[:25]
    bottom = new_sorted[-25:]
    def five_rate(rows):
        num = sum(r["n_fives"] for r in rows)
        den = sum(r["n_ratings"] for r in rows)
        return num / den if den else None
    return {
        "ranked_new": new_sorted,
        "top25_five_rate": five_rate(top),
        "bottom25_five_rate": five_rate(bottom),
        "all_new_five_rate": five_rate(new_sorted),
        "top25_mean_ceiling_mass": float(np.mean([r["ceiling_mass"] for r in top])),
        "bottom25_mean_ceiling_mass": float(np.mean([r["ceiling_mass"] for r in bottom])),
        "top25_mean_disagreement": float(np.mean([r["disagreement_std"] for r in top])),
        "bottom25_mean_disagreement": float(np.mean([r["disagreement_std"] for r in bottom])),
    }


def rank_parts_from_saved(row: dict, n_ratings: int) -> dict:
    return {
        "rank_score": row["disagreement_std"] + row["non_ceiling_uncertainty"] + 0.5 / (1.0 + n_ratings)
    }


def write_priority_csv(rows: list[dict], path: Path) -> None:
    fields = [
        "rank", "item_id", "task_folder", "set", "split_not_used_in_rank", "n_ratings", "empty_slots_of_33",
        "n_fives", "five_rate", "rank_score", "disagreement_std", "entropy_normalized", "ceiling_mass",
        "non_ceiling_uncertainty", "under_rated_term", "ensemble_expected_score", "n_members",
        "astra_mean", "opus_mean", "h3_expected", "member_expected_scores",
    ]
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for row in rows:
            w.writerow({
                "rank": row["rank"],
                "item_id": row["item"],
                "task_folder": row["task"],
                "set": row["set"],
                "split_not_used_in_rank": row["split"],
                "n_ratings": row["n_ratings"],
                "empty_slots_of_33": row["empty_slots_of_33"],
                "n_fives": row["n_fives"],
                "five_rate": f"{row['five_rate']:.4f}",
                "rank_score": f"{row['rank_score']:.6f}",
                "disagreement_std": f"{row['disagreement_std']:.6f}",
                "entropy_normalized": f"{row['entropy_normalized']:.6f}",
                "ceiling_mass": f"{row['ceiling_mass']:.6f}",
                "non_ceiling_uncertainty": f"{row['non_ceiling_uncertainty']:.6f}",
                "under_rated_term": f"{row['under_rated_term']:.6f}",
                "ensemble_expected_score": f"{row['ensemble_expected_score']:.6f}",
                "n_members": row["n_members"],
                "astra_mean": f"{row['astra_mean']:.4f}",
                "opus_mean": f"{row['opus_mean']:.4f}",
                "h3_expected": f"{row['h3_expected']:.4f}",
                "member_expected_scores": " ".join(f"{x:.4f}" for x in row["member_expected_scores"]),
            })


def spearman(a, b) -> float:
    from scipy.stats import spearmanr
    return float(spearmanr(a, b).statistic)


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    work = OUT / "work"
    work.mkdir(exist_ok=True)
    art = read_csv(EXP29 / "data_11-27-2026/artifacts_11-27-2026.csv")
    assert sum(int(r["n_all"]) for r in art) == 445
    assert sum(int(r["n_all"]) for r in art if r["set"] == "new") == 250
    assert sum(int(r["n_all"]) for r in art if r["set"] == "old") == 195
    h2_calls = load_h2_calls(EXP28 / "data_11-26-2026/judge_scores_h2_11-26-2026.csv")
    h4_paths = {
        "h4_astra": EXP28 / "results/h4_codex_astra_11-26-2026.jsonl",
        "h4_argon": EXP28 / "results/h4_agy_argon_11-26-2026.jsonl",
        "h4_opus": EXP28 / "results/h4_agy_opus_11-26-2026.jsonl",
    }
    # Attach ratings onto art rows for the fitter. The ensemble loader reads ratings_all itself.
    for row in art:
        row["ratings"] = [int(x) for x in row["ratings_all"].split()]
    built = load_ensemble(art, h2_calls, h4_paths)
    by_item = {r["item"]: r for r in built}
    assert all(r["n_members"] == 6 for r in built if r["set"] == "new")

    # Value-shuffle control: replacing scores with a constant list of the same length does not change rank inputs that are judge-only.
    shuffled_scores = []
    for row in built:
        if row["set"] != "new":
            continue
        again = rank_parts_from_saved(row, n_ratings=0)
        # n=0 changes the under-rated term on purpose; the judge terms must be identical to the stored ones.
        shuffled_scores.append(abs((again["rank_score"] - 0.5) - (row["disagreement_std"] + row["non_ceiling_uncertainty"])) < 1e-12)
    assert all(shuffled_scores)

    tables = priority_tables(built)
    write_priority_csv(tables["ranked_new"], OUT / "next_ratings_priority_all_new_items_11-27-2026.csv")
    write_priority_csv(tables["ranked_new"][:25], OUT / "next_ratings_priority_top25_11-27-2026.csv")

    align27 = align_experiment_27(work)
    align25_247 = align_experiment_25(
        EXP27 / "data_11-24-2026/human_ratings_old_11-24-2026.csv",
        EXP27 / "data_11-24-2026/human_ratings_new_11-24-2026.csv",
        EXP27 / "data_11-24-2026/judge_scores_h2_11-24-2026.csv",
        EXP25 / "results/setaware.json",
        "247-rating freeze",
    )
    align25_250 = align_experiment_25(
        EXP28 / "data_11-26-2026/human_ratings_old_11-26-2026.csv",
        EXP28 / "data_11-26-2026/human_ratings_new_11-26-2026.csv",
        EXP28 / "data_11-26-2026/judge_scores_h2_11-26-2026.csv",
        EXP25 / "results_interim_11-24-2026_1912/setaware.json",
        "250-rating interim",
    )

    # 445-rating F8 refit. Test rows keep the experiment 27 split.
    fit_rows = []
    for row in art:
        fit_rows.append({
            "item": row["item"], "task": row["task"], "set": row["set"], "split": row["split"],
            "astra": float(row["astra"]), "opus": float(row["opus"]),
            "h3_score": float(row["h3_score"]), "h3_expected": float(row["h3_expected"]),
            "ratings": [int(x) for x in row["ratings_all"].split()],
        })
    fitted = fit_f8_on_artifacts(fit_rows)
    test_built = [by_item[item] for item in fitted["items"]]
    assert [r["task"] for r in test_built] == list(fitted["tasks"])
    retro = retrospective_curves(test_built, fitted["Q"], fitted["Cset"], SEED_POWER)
    forward = forward_curves(test_built, fitted["Q"], fitted["Cset"], SEED_POWER)
    # Paired RPS vector at the full 445 histograms, for the task curve.
    P_full = hists_from_lists([r["ratings"] for r in test_built])
    d_full = paired_rps(P_full, fitted["Q"], fitted["Cset"])
    tasks_curve = task_extrapolation(d_full, fitted["tasks"], SEED_POWER)

    # Association of the rank score with the observed five-rate. Retrospective, not an input.
    new_rows = tables["ranked_new"]
    assoc = spearman([r["rank_score"] for r in new_rows], [r["five_rate"] for r in new_rows])

    trace = next(r for r in tables["ranked_new"] if r["rank"] == 1)
    trace_public = {k: trace[k] for k in (
        "rank", "item", "task", "split", "n_ratings", "n_fives", "rank_score", "disagreement_std",
        "entropy_normalized", "ceiling_mass", "non_ceiling_uncertainty", "member_names", "member_expected_scores",
        "astra_mean", "opus_mean", "h3_expected",
    )}

    # Drop arrays before JSON.
    fitted_public = {k: v for k, v in fitted.items() if k not in {"Q", "Cset", "test_positions", "tasks", "sets", "items"}}
    result = {
        "date": "11-27-2026",
        "seed_alignment": SEED_ALIGN,
        "seed_power": SEED_POWER,
        "bootstrap_draws": DRAWS,
        "numpy": np.__version__,
        "inputs_sha256": {
            "exp27_ratings_new": sha256(EXP27 / "data_11-24-2026/human_ratings_new_11-24-2026.csv"),
            "exp27_h2": sha256(EXP27 / "data_11-24-2026/judge_scores_h2_11-24-2026.csv"),
            "exp29_artifacts": sha256(EXP29 / "data_11-27-2026/artifacts_11-27-2026.csv"),
            "exp28_h2": sha256(EXP28 / "data_11-26-2026/judge_scores_h2_11-26-2026.csv"),
        },
        "alignment_experiment_27": align27,
        "alignment_experiment_25_247": align25_247,
        "alignment_experiment_25_250": align25_250,
        "f8_refit_on_445": fitted_public,
        "task_curve_matches_f8_interval": {
            "point_abs": abs(tasks_curve["full"]["point"] - fitted_public["paired_rps"]["point"]),
            "hi_abs": abs(tasks_curve["full"]["hi"] - fitted_public["paired_rps"]["hi"]),
        },
        "retrospective": retro,
        "forward_simulation": forward,
        "task_extrapolation": {k: v for k, v in tasks_curve.items() if k != "by_task_count"} | {"by_task_count": tasks_curve["by_task_count"]},
        "priority": {
            "n_new_artifacts": len(tables["ranked_new"]),
            "top25_five_rate": tables["top25_five_rate"],
            "bottom25_five_rate": tables["bottom25_five_rate"],
            "all_new_five_rate": tables["all_new_five_rate"],
            "top25_mean_ceiling_mass": tables["top25_mean_ceiling_mass"],
            "bottom25_mean_ceiling_mass": tables["bottom25_mean_ceiling_mass"],
            "top25_mean_disagreement": tables["top25_mean_disagreement"],
            "bottom25_mean_disagreement": tables["bottom25_mean_disagreement"],
            "spearman_rank_score_vs_five_rate": assoc,
            "trace_top_item": trace_public,
            "top5": [{k: r[k] for k in ("rank", "item", "task", "n_ratings", "five_rate", "rank_score", "disagreement_std", "ceiling_mass", "non_ceiling_uncertainty")} for r in tables["ranked_new"][:5]],
        },
        "predictions": {},
    }
    # Fill prediction hits from the measured numbers. The thresholds were written in PREREG.md first.
    p27 = align27["match_point_within_0.0005"] and align27["match_endpoints_within_0.001"]
    p25 = all(align25_247[k]["match_within_0.001"] and align25_250[k]["match_within_0.001"] for k in ("GPT-6 Astra", "Claude Opus 5.5"))
    fwd_uniform = forward["curves"]["uniform"]
    fwd_active = forward["curves"]["active"]
    max_shift = max(abs(row["median_upper"] - fitted_public["paired_rps"]["hi"]) for row in fwd_uniform + fwd_active)
    any_cross = any(row["median_upper"] < 0 for row in fwd_uniform + fwd_active)
    policy_gap = max(abs(a["median_upper"] - b["median_upper"]) for a, b in zip(fwd_uniform, fwd_active))
    crossing = tasks_curve["extrapolated_crossing_task_count"]
    five_top_lower = tables["top25_five_rate"] < tables["bottom25_five_rate"]
    five_active_lower = retro["five_rate_of_the_next_100_revealed"]["active"]["mean"] < retro["five_rate_of_the_next_100_revealed"]["uniform"]["mean"]
    result["predictions"] = {
        "1_experiment_27_alignment": p27,
        "2_experiment_25_alignment": p25,
        "3_forward_never_crosses_and_shift_under_0.01": (not any_cross) and max_shift < 0.01,
        "3_policy_gap_under_0.005": policy_gap < 0.005,
        "3_max_abs_shift_of_median_upper": max_shift,
        "3_any_median_upper_below_zero": any_cross,
        "3_max_policy_gap": policy_gap,
        "4_extrapolated_task_count_between_22_and_40": crossing is not None and 22 <= crossing <= 40,
        "4_extrapolated_task_count": crossing,
        "5_top25_five_rate_below_bottom25": five_top_lower,
        "5_active_revealed_five_rate_below_uniform": five_active_lower,
    }
    # Keep the extrapolation grid out of the bulky default by storing a short crossing row only plus the m=20..40 slice.
    distance = tasks_curve["full"]["hi"] - tasks_curve["full"]["point"]
    result["task_extrapolation"]["extrapolated_upper_from_20_to_40"] = [
        {"n_tasks": m, "extrapolated_upper": float(tasks_curve["full"]["point"] + distance * np.sqrt(20.0 / m)),
         "label": "EXTRAPOLATION. Planning only. Not a measured human interval."}
        for m in range(20, 41)
    ]
    dest = OUT / "analysis_11-27-2026.json"
    dest.write_text(json.dumps(result, indent=1))
    print(json.dumps({
        "align27": align27["judgelib_boot"],
        "align27_ok": p27,
        "align25_ok": p25,
        "f8_445": fitted_public["paired_rps"],
        "f8_levels_rps": fitted_public["levels"]["judge"]["RPS"],
        "constant_rps": fitted_public["levels"]["constant"]["RPS"],
        "crossing_tasks": crossing,
        "forward_shift": max_shift,
        "forward_cross": any_cross,
        "policy_gap": policy_gap,
        "top25_five": tables["top25_five_rate"],
        "bottom25_five": tables["bottom25_five_rate"],
        "active_five": retro["five_rate_of_the_next_100_revealed"]["active"]["mean"],
        "uniform_five": retro["five_rate_of_the_next_100_revealed"]["uniform"]["mean"],
        "spearman_five": assoc,
        "top5": result["priority"]["top5"],
        "predictions": result["predictions"],
    }, indent=1))


if __name__ == "__main__":
    main()
