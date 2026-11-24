"""Experiment 27: data loading, CE-fitted ordinal calibration, metrics and task-bootstrap (CPU, no model calls). Dated 11-24-2026.

Metrics follow exp 22/25: RPS = mean over 5 thresholds of (Qc-Pc)^2 + Pc(1-Pc); CE = -sum P log Q; TVD = half L1; per artifact, then equal weight per artifact.
Search stage never loads test rows (load(..., include_test=False)).
"""
import csv, json, re
from pathlib import Path
import numpy as np
from scipy import optimize, stats

EPS = 1e-6
FEATS = {  # feature sets of PREREG section 4
    "F1_astra": ["astra"], "F2_opus": ["opus"], "F3_both": ["astra", "opus"], "F4_both_gap": ["astra", "opus", "gap"],
    "F5_edit": ["edit"], "F6_both_edit": ["astra", "opus", "edit"], "F7_h3": ["h3s", "h3e"], "F8_both_h3": ["astra", "opus", "h3s", "h3e"],
    "F9_both_h3_set": ["astra", "opus", "h3s", "h3e", "isnew"], "F3s_both_set": ["astra", "opus", "isnew"],
}
SET_AWARE = {"F9_both_h3_set", "F3s_both_set"}


def hist(v):
    return np.bincount(np.asarray(v, dtype=int), minlength=6) / len(v)


def smooth(p, eps=EPS):
    p = np.maximum(np.asarray(p, float), eps)
    return p / p.sum(-1, keepdims=True)


def rps(P, Q):
    return np.mean((np.cumsum(Q, -1)[..., :5] - np.cumsum(P, -1)[..., :5]) ** 2 + np.cumsum(P, -1)[..., :5] * (1 - np.cumsum(P, -1)[..., :5]), -1)


def ce(P, Q):
    return -np.sum(np.where(P > 0, P * np.log(np.where(Q > 0, Q, 1)), 0.0), -1)


def tvd(P, Q):
    return 0.5 * np.abs(P - Q).sum(-1)


def parse_h3(raw):
    i = raw.find("{")
    try:
        o, _ = json.JSONDecoder().raw_decode(raw[i:])
        s = int(o["final_score_0_5"]); d = o["score_distribution"]
        p = np.array([float(d[str(k)]) for k in range(6)])
        if (p < 0).any() or abs(p.sum() - 1) > 0.05 or not 0 <= s <= 5:
            return None
        return s, p / p.sum()
    except Exception:
        return None


def load(data, h3_files=(), include_test=True):
    """Artifacts as dict of arrays. Test rows (ratings included) are dropped unless include_test."""
    split = {r["task"]: r["split"] for r in csv.DictReader(open(f"{data}/task_splits_11-24-2026.csv"))}
    rows = []
    for st in ("old", "new"):
        for r in csv.DictReader(open(f"{data}/human_ratings_{st}_11-24-2026.csv")):
            if r["split"] == "test" and not include_test:
                continue
            rat = [int(x) for x in r["ratings_sorted_0to5_rater_identity_removed"].split()]
            rows.append({"item": r["item"], "task": r["task"], "set": st, "split": r["split"], "ratings": rat})
    ix = {r["item"]: k for k, r in enumerate(rows)}
    js = {}
    for r in csv.DictReader(open(f"{data}/judge_scores_h2_11-24-2026.csv")):
        if r["item"] in ix:
            js.setdefault((r["item"], r["judge"]), []).append(int(r["score_0to5"]))
    ed = {r["item"]: float(r["edit_similarity"]) for r in csv.DictReader(open(f"{data}/edit_distance_feature_11-24-2026.csv"))}
    h3 = {}
    for fn in h3_files:
        for l in open(fn):
            o = json.loads(l)
            if o["status"] != "ok":
                continue
            it = o["id"].split("#r")[0]
            if it in ix:
                pr = parse_h3(o["raw_response"])
                if pr:
                    h3.setdefault(it, []).append(pr)
    n = len(rows)
    D = {"rows": rows, "n": n}
    D["P"] = np.array([hist(r["ratings"]) for r in rows]); D["C"] = np.array([np.bincount(r["ratings"], minlength=6) for r in rows], float)
    D["task"] = np.array([r["task"] for r in rows]); D["set"] = np.array([r["set"] for r in rows]); D["split"] = np.array([r["split"] for r in rows])
    astra = [js[(r["item"], "H2_astra")] for r in rows]; opus = [js[(r["item"], "H2_opus")] for r in rows]
    D["astra"] = np.array([np.mean(a) for a in astra]); D["opus"] = np.array([np.mean(a) for a in opus])
    D["gap"] = np.abs(D["astra"] - D["opus"]); D["edit"] = np.array([ed[r["item"]] for r in rows]); D["isnew"] = (D["set"] == "new").astype(float)
    D["H2raw"] = smooth(np.array([hist(a + o) for a, o in zip(astra, opus)]))
    D["h3s"] = np.array([np.mean([s for s, _ in h3[r["item"]]]) if r["item"] in h3 else np.nan for r in rows])
    D["h3e"] = np.array([np.mean([p @ np.arange(6) for _, p in h3[r["item"]]]) if r["item"] in h3 else np.nan for r in rows])
    D["h3p"] = np.array([np.mean([p for _, p in h3[r["item"]]], 0) if r["item"] in h3 else np.full(6, np.nan) for r in rows])
    sol = [js.get((r["item"], "H2_sol")) for r in rows]
    D["H2sol_opus_raw"] = np.array([smooth(hist(s_ + o)) if s_ is not None else np.full(6, np.nan) for s_, o in zip(sol, opus)])
    return D


def marginal(C):
    c = C.sum(0)
    return smooth(c / c.sum())


class Ordinal:
    """P(r<=k) = sigmoid(theta_k - w.x); fitted by minimising mean per-artifact CE to the human histograms + alpha/2 |w|^2; optional mixture m with a constant."""

    def __init__(self, cols, alpha=1.0, m=0.0):
        self.cols, self.alpha, self.m = cols, alpha, m

    def _x(self, D, idx):
        return np.column_stack([D[c][idx] for c in self.cols]) if self.cols else np.zeros((len(idx), 0))

    def _q(self, th, w, X):
        z = th[None, :] - (X @ w)[:, None]
        F = 1 / (1 + np.exp(-z))
        F = np.concatenate([np.zeros((len(X), 1)), F, np.ones((len(X), 1))], 1)
        return np.diff(F, axis=1)

    def _unpack(self, v):
        th = np.cumsum(np.concatenate([[v[0]], np.exp(v[1:5])]))
        return th, v[5:]

    def fit(self, D, idx):
        X = self._x(D, idx); self.mu, self.sd = X.mean(0), X.std(0) + 1e-9
        Xs = (X - self.mu) / self.sd; P = D["P"][idx]
        self.const = marginal(D["C"][idx])
        c = np.clip(np.cumsum(self.const)[:5], 1e-4, 1 - 1e-4); th0 = np.log(c / (1 - c))
        v0 = np.concatenate([[th0[0]], np.log(np.maximum(np.diff(th0), 1e-3)), np.zeros(Xs.shape[1])])

        def loss(v):
            th, w = self._unpack(v)
            Q = (1 - self.m) * self._q(th, w, Xs) + self.m * self.const
            return ce(P, smooth(Q)).mean() + 0.5 * self.alpha * (w @ w)

        r = optimize.minimize(loss, v0, method="L-BFGS-B")
        self.v = r.x; self.train_ce = float(r.fun)
        return self

    def predict(self, D, idx):
        X = (self._x(D, idx) - self.mu) / self.sd
        th, w = self._unpack(self.v)
        return smooth((1 - self.m) * self._q(th, w, X) + self.m * self.const)


class Direct:
    """Q proportional to p^beta * const^gamma (p = verbalised H3 distribution floored at 1e-3), beta, gamma >= 0 fitted by CE."""

    def __init__(self, alpha=0.0, m=0.0):
        self.cols = ["h3p"]; self.alpha = alpha; self.m = m

    def _q(self, p, b, g):
        L = b * np.log(np.maximum(p, 1e-3)) + g * np.log(self.const)[None, :]
        L -= L.max(1, keepdims=True); Q = np.exp(L); return Q / Q.sum(1, keepdims=True)

    def fit(self, D, idx):
        self.const = marginal(D["C"][idx]); p = D["h3p"][idx]; P = D["P"][idx]
        r = optimize.minimize(lambda v: ce(P, smooth(self._q(p, np.exp(v[0]), np.exp(v[1])))).mean(), [0.0, -1.0], method="L-BFGS-B")
        self.v = r.x; self.train_ce = float(r.fun); return self

    def predict(self, D, idx):
        return smooth(self._q(D["h3p"][idx], np.exp(self.v[0]), np.exp(self.v[1])))


def metrics_rows(P, Q):
    return {"RPS": rps(P, Q), "CE": ce(P, Q), "TVD": tvd(P, Q)}


def corr(Q, P):
    qm = Q @ np.arange(6); pm = P @ np.arange(6)
    if np.ptp(qm) == 0 or np.ptp(pm) == 0:
        return np.nan, np.nan
    return float(stats.spearmanr(qm, pm)[0]), float(np.corrcoef(qm, pm)[0, 1])


def boot(tasks, fn, draws=10000, seed=20261124):
    """Task bootstrap: fn(index array) -> dict of floats. Returns point, 95% percentile interval, and the draws (for paired differences)."""
    rng = np.random.default_rng(seed)
    ut = np.array(sorted(set(tasks))); groups = [np.where(tasks == t)[0] for t in ut]
    point = fn(np.arange(len(tasks)))
    out = {k: [] for k in point}
    for _ in range(draws):
        pick = rng.integers(0, len(ut), len(ut))
        idx = np.concatenate([groups[i] for i in pick])
        o = fn(idx)
        for k, v in o.items():
            out[k].append(v)
    arr = {k: np.array(v) for k, v in out.items()}
    ci = {k: (float(np.nanpercentile(v, 2.5)), float(np.nanpercentile(v, 97.5))) for k, v in arr.items()}
    return point, ci, arr
