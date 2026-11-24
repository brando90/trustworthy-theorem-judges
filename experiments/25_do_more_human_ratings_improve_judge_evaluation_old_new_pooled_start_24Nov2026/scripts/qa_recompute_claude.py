"""Independent QA recomputation (Claude Opus 5.5, 11-24-2026). Reads only qa_input.json."""
import json, sys
import numpy as np

d = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "qa_input.json"))
EPS = 1e-6


def hist(xs):
    h = np.bincount(np.asarray(xs, int), minlength=6).astype(float)
    return h / h.sum()


def floor_norm(q):
    q = np.maximum(q, EPS)
    return q / q.sum()


def rps(p, q):
    cp, cq = np.cumsum(p)[:5], np.cumsum(q)[:5]
    return float(np.mean((cq - cp) ** 2 + cp * (1 - cp)))


def ce(p, q):
    m = p > 0
    return float(-np.sum(p[m] * np.log(q[m])))


def tvd(p, q):
    return float(0.5 * np.abs(p - q).sum())


def rankavg(x):
    x = np.asarray(x, float)
    order = np.argsort(x, kind="mergesort")
    r = np.empty(len(x))
    r[order] = np.arange(1, len(x) + 1)
    for v in np.unique(x):
        m = x == v
        r[m] = r[m].mean()
    return r


def pearson(a, b):
    a, b = np.asarray(a, float), np.asarray(b, float)
    return float(np.corrcoef(a, b)[0, 1])


def spearman(a, b):
    return pearson(rankavg(a), rankavg(b))


def const_q(art, pool):
    """Leave-one-task-out pooled human histogram over `pool` artifacts."""
    rs = [r for o in pool if o["task"] != art["task"] for r in o["ratings"]]
    return floor_norm(hist(rs))


sets = {"old": [a for a in d if a["set"] == "old"],
        "new": [a for a in d if a["set"] == "new"],
        "both": list(d)}

# Precompute constant baselines per artifact
for a in d:
    a["P"] = hist(a["ratings"])
    a["rps_const_set"] = rps(a["P"], const_q(a, sets[a["set"]]))
    a["rps_const_pooled"] = rps(a["P"], const_q(a, d))
    for j in ("astra", "opus"):
        q = floor_norm(hist(a[j]))
        a[f"{j}_rps"] = rps(a["P"], q)
        a[f"{j}_ce"] = ce(a["P"], q)
        a[f"{j}_tvd"] = tvd(a["P"], q)

res = {"meta": {"writer": "Claude Opus 5.5 (claude-opus-5-5)", "date": "11-24-2026",
                "n_total": len(d)}, "rows": {}}
for j in ("astra", "opus"):
    for s, arts in sets.items():
        hm = [np.mean(a["ratings"]) for a in arts]
        jm = [np.mean(a[j]) for a in arts]
        row = {
            "n": len(arts),
            "n_tasks": len({a["task"] for a in arts}),
            "RPS": float(np.mean([a[f"{j}_rps"] for a in arts])),
            "CE": float(np.mean([a[f"{j}_ce"] for a in arts])),
            "TVD": float(np.mean([a[f"{j}_tvd"] for a in arts])),
            "Spearman": spearman(jm, hm),
            "Pearson": pearson(jm, hm),
            "const_RPS_setaware": float(np.mean([a["rps_const_set"] for a in arts])),
        }
        if s == "both":
            row["const_RPS_pooled"] = float(np.mean([a["rps_const_pooled"] for a in arts]))
        res["rows"][f"{j}/{s}"] = row

# Task bootstrap of RPS, set new
def task_boot(arts, key, B=2000, seed=1):
    rng = np.random.default_rng(seed)
    tasks = sorted({a["task"] for a in arts})
    by = {t: [a[key] for a in arts if a["task"] == t] for t in tasks}
    out = np.empty(B)
    for b in range(B):
        pick = rng.integers(0, len(tasks), len(tasks))
        vals = [v for i in pick for v in by[tasks[i]]]
        out[b] = np.mean(vals)  # artifact-weighted mean within the resample
    return [float(np.percentile(out, 2.5)), float(np.percentile(out, 97.5))]

res["bootstrap_new_RPS_95"] = {}
for key in ("astra_rps", "opus_rps", "rps_const_set"):
    res["bootstrap_new_RPS_95"][key] = task_boot(sets["new"], key)

# Split-half human-vs-human RPS
def split_half(arts, n_splits=200, seed=1, mode="small_is_P", floorQ=True):
    rng = np.random.default_rng(seed)
    elig = [a for a in arts if len(a["ratings"]) >= 2]
    per_split = []
    for _ in range(n_splits):
        vals = []
        for a in elig:
            r = rng.permutation(a["ratings"])
            k = len(r) // 2
            A, Bh = hist(r[:k]), hist(r[k:])  # A = smaller half when n odd
            fq = floor_norm if floorQ else (lambda x: x)
            if mode == "small_is_P":
                vals.append(rps(A, fq(Bh)))
            elif mode == "large_is_P":
                vals.append(rps(Bh, fq(A)))
            else:  # symmetric average
                vals.append(0.5 * (rps(A, fq(Bh)) + rps(Bh, fq(A))))
        per_split.append(np.mean(vals))
    return {"n_eligible": len(elig), "mean_RPS": float(np.mean(per_split)),
            "sd_over_splits": float(np.std(per_split))}

res["split_half"] = {}
for s, arts in sets.items():
    res["split_half"][s] = {m: split_half(arts, mode=m) for m in
                            ("small_is_P", "large_is_P", "symmetric")}
    res["split_half"][s]["small_is_P_noFloor"] = split_half(arts, floorQ=False)

json.dump(res, open("qa_result.json", "w"), indent=2)

hdr = f"{'row':12s} {'n':>4s} {'RPS':>7s} {'CE':>7s} {'TVD':>7s} {'Spear':>7s} {'Pear':>7s} {'cRPS_set':>8s} {'cRPS_pool':>9s}"
print(hdr)
for k, r in res["rows"].items():
    print(f"{k:12s} {r['n']:4d} {r['RPS']:7.4f} {r['CE']:7.4f} {r['TVD']:7.4f} {r['Spearman']:7.4f} "
          f"{r['Pearson']:7.4f} {r['const_RPS_setaware']:8.4f} {r.get('const_RPS_pooled', float('nan')):9.4f}")
print("Bootstrap 95% (set new, 25 tasks, 2000 draws, seed 1):", res["bootstrap_new_RPS_95"])
for s, v in res["split_half"].items():
    print("split-half", s, {m: (x["n_eligible"], round(x["mean_RPS"], 4)) for m, x in v.items()})
