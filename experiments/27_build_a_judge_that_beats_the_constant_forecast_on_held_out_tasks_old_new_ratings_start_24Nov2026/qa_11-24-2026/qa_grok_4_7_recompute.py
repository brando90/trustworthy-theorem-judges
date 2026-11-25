import json
import numpy as np
from scipy.optimize import minimize
from scipy.special import expit, softplus
from scipy.stats import pearsonr, spearmanr

arts = json.load(open("qa_input.json"))
K = np.arange(6)
EPS = 1e-6

def floor_renorm(q):
    q = np.maximum(np.asarray(q, float), EPS)
    return q / q.sum()

def P_of(a):
    h = np.bincount(np.asarray(a["ratings"], int), minlength=6).astype(float)
    return h / h.sum()

def pack_metrics(P, Q, ce_floor=True):
    Q = np.asarray(Q, float)
    cp, cq = np.cumsum(P)[:-1], np.cumsum(Q)[:-1]
    rps = np.mean((cq - cp) ** 2 + cp * (1 - cp))
    Qf = floor_renorm(Q) if ce_floor else Q
    ce = -np.sum(P * np.log(Qf), where=P > 0, initial=0.0)
    return rps, ce, 0.5 * np.sum(np.abs(P - Q))

def hist_ratings(rows):
    c = np.zeros(6)
    for a in rows:
        c += np.bincount(np.asarray(a["ratings"], int), minlength=6)
    return floor_renorm(c / c.sum())

def h2_of(a):
    s = np.r_[np.asarray(a["astra"], int), np.asarray(a["opus"], int)]
    return floor_renorm(np.bincount(s, minlength=6).astype(float))

tv = [a for a in arts if a["split"] in ("train", "val")]
const_set = {s: hist_ratings([a for a in tv if a["set"] == s]) for s in ("old", "new")}
const_pool = hist_ratings(tv)
uniform = np.full(6, 1.0 / 6.0)
test = [a for a in arts if a["split"] == "test"]
P = np.stack([P_of(a) for a in test])
Qs = {
    "final_Q": np.stack([np.asarray(a["final_Q"], float) for a in test]),
    "constant_set": np.stack([const_set[a["set"]] for a in test]),
    "constant_pooled": np.repeat(const_pool[None], len(test), 0),
    "uniform": np.repeat(uniform[None], len(test), 0),
    "h2": np.stack([h2_of(a) for a in test]),
}
raw = {k: np.array([pack_metrics(P[i], Qs[k][i]) for i in range(len(test))]) for k in Qs}
hm = np.array([np.mean(a["ratings"]) for a in test])
sets = np.array([a["set"] for a in test])
names = ("pooled", "old", "new")
masks = {"pooled": np.ones(len(test), bool), "old": sets == "old", "new": sets == "new"}

def corr(qmean, y):
    if len(y) < 3 or np.unique(qmean).size < 2 or np.unique(y).size < 2:
        return None, None
    return float(pearsonr(qmean, y).statistic), float(spearmanr(qmean, y).statistic)

metrics = {}
for name, m in masks.items():
    metrics[name] = {}
    for k, M in raw.items():
        rec = {s: float(M[m, i].mean()) for i, s in enumerate(("RPS", "CE", "TVD"))}
        if k in ("final_Q", "h2"):
            rec["pearson"], rec["spearman"] = corr(Qs[k][m] @ K, hm[m])
        metrics[name] = {**metrics[name], k: rec}

tasks = sorted({a["task"] for a in test})
groups = [[i for i, a in enumerate(test) if a["task"] == t] for t in tasks]
gsum = {k: np.array([M[ix].sum(0) for ix in groups]) for k, M in raw.items()}
gcnt = np.array([len(ix) for ix in groups])
rng = np.random.default_rng(20261124)
draw = rng.integers(0, len(tasks), size=(10000, len(tasks)))
den = gcnt[draw].sum(1)
boot = {}
for label, base in (("final_minus_constant_set", "constant_set"), ("final_minus_h2", "h2")):
    point = (gsum["final_Q"].sum(0) - gsum[base].sum(0)) / gcnt.sum()
    diffs = (gsum["final_Q"][draw].sum(1) - gsum[base][draw].sum(1)) / den[:, None]
    lo, hi = np.percentile(diffs, [2.5, 97.5], axis=0)
    boot[label] = {s: {"point": float(point[i]), "lo": float(lo[i]), "hi": float(hi[i])}
                   for i, s in enumerate(("RPS", "CE", "TVD"))}

by_task = {}
for a in arts:
    by_task.setdefault(a["task"], set()).add(a["split"])
multi = sorted(t for t, sp in by_task.items() if len(sp) > 1)
n_empty = sum(len(a["ratings"]) < 1 for a in arts)
bad_q, max_dev = [], 0.0
for a in test:
    dev = abs(float(np.sum(a["final_Q"])) - 1.0)
    max_dev = max(max_dev, dev)
    if dev > 1e-6:
        bad_q.append(a["id"])
counts = {}
for sp in ("train", "val", "test"):
    counts[sp] = {}
    for st in ("old", "new"):
        rows = [a for a in arts if a["split"] == sp and a["set"] == st]
        counts[sp][st] = {"artifacts": len(rows), "tasks": len({a["task"] for a in rows})}
leakage = {"tasks_in_multiple_splits": multi, "artifacts_lt_1_rating": n_empty,
           "final_Q_not_sum_to_1": bad_q, "max_abs_final_Q_sum_dev": max_dev, "counts": counts}

def feats(rows):
    return np.array([[np.mean(a["astra"]), np.mean(a["opus"]), a["h3_score"], a["h3_expected"]] for a in rows])

Xtv, Xte = feats(tv), feats(test)
mu, sd = Xtv.mean(0), Xtv.std(0)
sd = np.where(sd == 0, 1.0, sd)
Ztv, Zte = (Xtv - mu) / sd, (Xte - mu) / sd
Ptv = np.stack([P_of(a) for a in tv])
cp = np.clip(np.cumsum(Ptv.mean(0))[:-1], 1e-3, 1 - 1e-3)
p0 = np.r_[np.zeros(4), np.log(cp[0] / (1 - cp[0])), np.log(np.diff(np.r_[np.log(cp / (1 - cp)), [0]])[:-1] + 1e-2)]

def unpack(p):
    th = np.empty(5)
    th[0] = p[4]
    th[1:] = p[4] + np.cumsum(softplus(p[5:]))
    return p[:4], th

def pmf(Z, p):
    w, th = unpack(p)
    cdf = expit(th[None] - (Z @ w)[:, None])
    Q = np.empty((len(Z), 6))
    Q[:, 0], Q[:, 1:5], Q[:, 5] = cdf[:, 0], np.diff(cdf, axis=1), 1 - cdf[:, -1]
    Q = np.clip(Q, 0, None)
    return Q / Q.sum(1, keepdims=True)

def loss(p):
    Q = np.maximum(pmf(Ztv, p), EPS)
    Q /= Q.sum(1, keepdims=True)
    return -np.mean(np.sum(Ptv * np.log(Q), axis=1))

opt = minimize(loss, p0, method="L-BFGS-B", options={"maxiter": 400})
Qref = pmf(Zte, opt.x)
ref_m = np.array([pack_metrics(P[i], Qref[i]) for i in range(len(test))])
refit = {"success": bool(opt.success), "trainval_CE": float(opt.fun),
         "test_pooled": {s: float(ref_m[:, i].mean()) for i, s in enumerate(("RPS", "CE", "TVD"))},
         "final_Q_pooled": {s: metrics["pooled"]["final_Q"][s] for s in ("RPS", "CE", "TVD")}}
refit["refit_minus_final"] = {s: refit["test_pooled"][s] - refit["final_Q_pooled"][s] for s in ("RPS", "CE", "TVD")}

out = {"metrics": metrics, "bootstrap": boot, "leakage": leakage, "refit": refit}
json.dump(out, open("qa_result.json", "w"), indent=2)
print(f"{'subset':8} {'forecast':16} {'RPS':10} {'CE':10} {'TVD':10} {'pearson':10} {'spearman':10}")
for name in names:
    for k, rec in metrics[name].items():
        pr, sp = rec.get("pearson"), rec.get("spearman")
        print(f"{name:8} {k:16} {rec['RPS']:10.6f} {rec['CE']:10.6f} {rec['TVD']:10.6f} "
              f"{'':10}" if pr is None else f"{name:8} {k:16} {rec['RPS']:10.6f} {rec['CE']:10.6f} {rec['TVD']:10.6f} {pr:10.4f} {sp:10.4f}")
print("paired bootstrap 95% (task resample, artifact-weighted)")
for label, d in boot.items():
    for s, v in d.items():
        print(f"{label:28} {s:4} point={v['point']:.6f} [{v['lo']:.6f}, {v['hi']:.6f}]")
print("leakage multi_split", multi, "empty_ratings", n_empty, "bad_final_Q", len(bad_q), "max_dev", max_dev)
for sp, stv in counts.items():
    for st, c in stv.items():
        print(f"count {sp:5} {st:3} artifacts={c['artifacts']} tasks={c['tasks']}")
print("refit", refit["success"], "test", refit["test_pooled"], "minus_final", refit["refit_minus_final"])
