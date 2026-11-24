#!/usr/bin/env python3
"""Experiment 25: evaluate judges on old, new and pooled human ratings (RPS, CE, TVD, Spearman, Pearson), ceiling, learning curve.

Dated 11-24-2026. CPU only. Private inputs (individual ratings, rater ids) are read from paths given on the command line and are
never written; only aggregates go to --out. Run: python3 analyze.py --old-dataset P --exp21-scores P --sheets DIR --new-judge NAME=FILE ... --out results
"""
import argparse, csv, glob, json, re, sys, collections
from pathlib import Path
import numpy as np
from scipy import stats
sys.path.insert(0, str(Path(__file__).parent))
from evalcore import hist, smooth, per_artifact, floor_art, rps_art, loto_constant, corr_pair, boot_tasks

OLD_JUDGES = ["H0_sol", "H0_opus", "H1_sol", "H2_sol", "H2_opus", "H2_astra", "H2_sol61", "H2_argon"]
SCORE_RE = re.compile(r'"final_score_0_5"\s*:\s*(\d)')


def load_old(dataset_json, exp21_csv):
    d = json.load(open(dataset_json))
    rows = d["rows"]
    ds = {"items": [r["item"] for r in rows], "tasks": [r["task"] for r in rows],
          "ratings": [list(r["ratings"]) for r in rows], "raters": [list(range(len(r["ratings"]))) for r in rows], "judges": {}}
    for j, mat in d["outputs"].items():
        ds["judges"][j] = [list(map(int, m)) for m in mat]
    by = collections.defaultdict(dict)
    for r in csv.DictReader(open(exp21_csv)):
        if r["status"] == "COMPLETE":
            by[(r["judge"], r["item"])][int(r["repeat"])] = int(r["score_0to5"])
    for j in ("H2_astra", "H2_sol61", "H2_argon"):
        ds["judges"][j] = [[by[(j, it)][k] for k in (1, 2, 3)] for it in ds["items"]]
    return ds


def load_new(sheets_dir, judge_files):
    items, task, ratings, raters = [], {}, collections.defaultdict(list), collections.defaultdict(list)
    n_rows = n_blank = n_invalid = 0
    per_rater = collections.Counter()
    for f in sorted(glob.glob(f"{sheets_dir}/*.tsv")):
        rows = list(csv.reader(open(f), delimiter="\t"))
        h = rows[0]
        i = [k for k, x in enumerate(h) if x.startswith("final_score")][0]
        for r in rows[1:]:
            if len(r) < 5:
                continue
            n_rows += 1
            task[r[2]] = r[3]
            v = r[i].strip() if len(r) > i else ""
            if v == "":
                n_blank += 1
                continue
            try:
                x = float(v)
                assert x == int(x) and 0 <= x <= 5
            except Exception:
                n_invalid += 1
                continue
            ratings[r[2]].append(int(x)); raters[r[2]].append(r[1]); per_rater[r[1]] += 1
    order = sorted(task)
    ds = {"items": order, "tasks": [task[i] for i in order], "ratings": [ratings.get(i, []) for i in order],
          "raters": [raters.get(i, []) for i in order], "judges": {}, "per_rater_counts": dict(per_rater),
          "rows": n_rows, "blank": n_blank, "invalid": n_invalid}
    for name, fn in judge_files.items():
        got = collections.defaultdict(dict)
        for l in open(fn):
            r = json.loads(l)
            if r["status"] != "ok":
                continue
            m = set(SCORE_RE.findall(r["raw_response"]))
            if len(m) != 1:
                continue
            it, rep = r["id"].split("#r")
            got[it][int(rep)] = int(m.pop())
        ds["judges"][name] = [[got[it][k] for k in (1, 2, 3)] if len(got.get(it, {})) == 3 else None for it in order]
    return ds


def subset(ds, keep_idx, judge_names):
    d = {"items": [ds["items"][i] for i in keep_idx], "tasks": [ds["tasks"][i] for i in keep_idx],
         "ratings": [ds["ratings"][i] for i in keep_idx], "raters": [ds["raters"][i] for i in keep_idx], "judges": {}}
    for j in judge_names:
        d["judges"][j] = [ds["judges"][j][i] for i in keep_idx]
    return d


def pool(a, b, mapping):
    """mapping: pooled judge name -> (name in a, name in b)."""
    d = {k: a[k] + b[k] for k in ("items", "tasks", "ratings", "raters")}
    d["judges"] = {n: a["judges"][x] + b["judges"][y] for n, (x, y) in mapping.items()}
    return d


def arrays(ds, judge, min_ratings=1, calls=None):
    keep = [i for i, r in enumerate(ds["ratings"]) if len(r) >= min_ratings and ds["judges"][judge][i] is not None]
    P = np.array([hist(ds["ratings"][i]) for i in keep])
    C = np.array([np.bincount(ds["ratings"][i], minlength=6) for i in keep], float)
    Qj = np.array([hist(ds["judges"][judge][i]) for i in keep])
    jm = np.array([np.mean(ds["judges"][judge][i]) for i in keep]) / 5
    hm = np.array([np.mean(ds["ratings"][i]) for i in keep]) / 5
    tasks = np.array([ds["tasks"][i] for i in keep])
    return keep, P, C, smooth(Qj), jm, hm, tasks


def evaluate(ds, judge, min_ratings=1, draws=10000):
    keep, P, C, Q, jm, hm, tasks = arrays(ds, judge, min_ratings)
    Qc = loto_constant(C, tasks)
    Qu = np.full_like(P, 1 / 6)
    pa = per_artifact(P, Q); pc_ = per_artifact(P, Qc); pu = per_artifact(P, Qu)

    def fn(idx):
        o = {k: float(v[idx].mean()) for k, v in pa.items()}
        s, p = corr_pair(jm[idx], hm[idx])
        o["Spearman"], o["Pearson"] = s, p
        o["constant_RPS"] = float(pc_["RPS"][idx].mean())
        o["uniform_RPS"] = float(pu["RPS"][idx].mean())
        o["dRPS_vs_constant"] = o["RPS"] - o["constant_RPS"]
        o["dCE_vs_constant"] = o["CE"] - float(pc_["CE"][idx].mean())
        o["dTVD_vs_constant"] = o["TVD"] - float(pc_["TVD"][idx].mean())
        return o

    point, ci = boot_tasks(tasks, fn, draws)
    out = {"n_artifacts": len(keep), "n_tasks": len(set(tasks)), "n_ratings": int(C.sum()),
           "ratings_per_artifact_mean": float(C.sum() / len(keep))}
    for k in point:
        out[k] = {"est": float(point[k]), "lo": ci[k][0], "hi": ci[k][1]}
    return out


def ceiling(ds, splits=1000, seed=7):
    rng = np.random.default_rng(seed)
    idx = [i for i, r in enumerate(ds["ratings"]) if len(r) >= 2]
    tasks = [ds["tasks"][i] for i in idx]
    rps_v, sp, pe = [], [], []
    for _ in range(splits):
        A, B, a_m, b_m = [], [], [], []
        for i in idx:
            r = np.array(ds["ratings"][i]); perm = rng.permutation(len(r)); h = len(r) // 2
            ra, rb = r[perm[:h]], r[perm[h:]]
            A.append(hist(ra)); B.append(hist(rb)); a_m.append(ra.mean()); b_m.append(rb.mean())
        A, B = np.array(A), np.array(B)
        rps_v.append(float(np.mean(rps_art(A, B))))
        s, p = corr_pair(np.array(a_m), np.array(b_m)); sp.append(s); pe.append(p)
    r_half = float(np.nanmean(pe))
    sb = 2 * r_half / (1 + r_half)
    P = np.array([hist(ds["ratings"][i]) for i in idx])
    return {"n_artifacts": len(idx), "n_tasks": len(set(tasks)),
            "mean_raters": float(np.mean([len(ds["ratings"][i]) for i in idx])),
            "split_half_RPS_mean": float(np.mean(rps_v)), "split_half_Spearman_mean": float(np.nanmean(sp)),
            "split_half_Pearson_mean": r_half, "spearman_brown_full_reliability": sb,
            "correlation_ceiling_sqrt_reliability": float(np.sqrt(max(sb, 0))),
            "irreducible_RPS_floor_empirical": float(floor_art(P).mean())}


def learning_curve(ds, judge, ks, subsets=40, draws=200, min_ratings=1, seed=11):
    keep, P, C, Q, jm, hm, tasks = arrays(ds, judge, min_ratings)
    pa = per_artifact(P, Q)
    ut = np.array(sorted(set(tasks)))
    rng = np.random.default_rng(seed)
    out = {}
    for k in ks:
        if k > len(ut):
            continue
        est = {"RPS": [], "Spearman": []}; wid = {"RPS": [], "Spearman": []}
        for s in range(subsets):
            sel = rng.choice(ut, k, replace=False)
            idx = np.where(np.isin(tasks, sel))[0]

            def fn(ix, idx=idx):
                g = idx[ix]
                return {"RPS": float(pa["RPS"][g].mean()), "Spearman": corr_pair(jm[g], hm[g])[0]}
            point, ci = boot_tasks(tasks[idx], fn, draws, seed=int(rng.integers(1 << 30)))
            for m in est:
                est[m].append(point[m]); wid[m].append(ci[m][1] - ci[m][0])
        out[str(k)] = {m: {"mean_ci_width": float(np.nanmean(wid[m])), "sd_of_estimate": float(np.nanstd(est[m])),
                           "mean_estimate": float(np.nanmean(est[m]))} for m in est}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--old-dataset", required=True); ap.add_argument("--exp21-scores", required=True)
    ap.add_argument("--sheets", required=True); ap.add_argument("--new-judge", action="append", default=[])
    ap.add_argument("--pair", action="append", default=[], help="pooled=oldname:newname")
    ap.add_argument("--out", required=True); ap.add_argument("--draws", type=int, default=10000)
    ap.add_argument("--min-new-ratings", type=int, default=2)
    a = ap.parse_args()
    old = load_old(a.old_dataset, a.exp21_scores)
    new = load_new(a.sheets, dict(x.split("=", 1) for x in a.new_judge))
    res = {"min_new_ratings": a.min_new_ratings}
    nr = [len(r) for r in new["ratings"]]
    res["inventory_new"] = {"artifacts_assigned": len(new["items"]), "tasks": len(set(new["tasks"])), "rows_read": new["rows"],
        "rating_rows_filled": new["rows"] - new["blank"] - new["invalid"], "blank_rows": new["blank"], "invalid_rows": new["invalid"],
        "raters_with_any_rating": len(new["per_rater_counts"]),
        "ratings_per_rater_sorted": sorted(new["per_rater_counts"].values(), reverse=True),
        "artifacts_by_n_ratings": {str(k): v for k, v in sorted(collections.Counter(nr).items())}}
    res["inventory_old"] = {"artifacts": len(old["items"]), "tasks": len(set(old["tasks"])), "ratings": sum(map(len, old["ratings"]))}
    # table 1: old judges alone
    res["old"] = {j: evaluate(old, j, 1, a.draws) for j in OLD_JUDGES}
    mixj = [old["judges"]["H2_sol"][i] + old["judges"]["H2_opus"][i] for i in range(len(old["items"]))]
    old["judges"]["H2_sol+H2_opus(6 calls)"] = mixj
    res["old"]["H2_sol+H2_opus(6 calls)"] = evaluate(old, "H2_sol+H2_opus(6 calls)", 1, a.draws)
    pairs = dict(x.split("=", 1) for x in a.pair)  # pooled name -> "oldname:newname"
    res["new"], res["pooled"], res["old_same_judges"] = {}, {}, {}
    for nm, v in pairs.items():
        o, n = v.split(":")
        res["new"][nm] = evaluate(new, n, a.min_new_ratings, a.draws)
        res["old_same_judges"][nm] = res["old"][o]
        keep_new = [i for i, r in enumerate(new["ratings"]) if len(r) >= a.min_new_ratings and new["judges"][n][i] is not None]
        pooled = pool(old, subset(new, keep_new, [n]), {nm: (o, n)})
        res["pooled"][nm] = evaluate(pooled, nm, 1, a.draws)
    res["ceiling"] = {"old": ceiling(old), "new": ceiling(subset(new, [i for i, r in enumerate(new["ratings"]) if len(r) >= 2], [])),
                      "new_all_ge2": None}
    first = next(iter(pairs), None)
    if first:
        o, n = pairs[first].split(":")
        keep_new = [i for i, r in enumerate(new["ratings"]) if len(r) >= a.min_new_ratings and new["judges"][n][i] is not None]
        pooled = pool(old, subset(new, keep_new, [n]), {first: (o, n)})
        pool_h = {"items": pooled["items"], "tasks": pooled["tasks"], "ratings": pooled["ratings"], "raters": pooled["raters"]}
        res["ceiling"]["pooled"] = ceiling(pool_h)
        res["learning_curve"] = {"judge": first,
            "old": learning_curve(old, o, [5, 10, 15, 20, 25]),
            "new": learning_curve(subset(new, keep_new, [n]), n, [5, 10, 15, 20, 25], min_ratings=1),
            "pooled": learning_curve(pooled, first, [5, 10, 15, 20, 25, 30, 40, 50])}
    Path(a.out).mkdir(parents=True, exist_ok=True)
    json.dump(res, open(Path(a.out) / "aggregates.json", "w"), indent=1)
    print("wrote", Path(a.out) / "aggregates.json")


if __name__ == "__main__":
    main()
