"""Cumulative-logit and log-pool heads, proper scores, and task bootstrap.

Dated 11-27-2026. CPU only. The cross-entropy cumulative-logit head matches
experiment 27's Ordinal class at temperature 1 (same threshold parameterization,
same L2 term, same start). Ranked probability score uses the same normalized
five-threshold form as experiments 22, 25, 27 and 28.
"""
from __future__ import annotations

import numpy as np
from scipy import optimize, stats

EPS = 1e-6
SCORES = np.arange(6, dtype=float)
ALPHAS = (0.0, 0.1, 1.0, 10.0)
MIXES = (0.0, 0.25, 0.5)
OBJECTIVES = ("ce", "rps")
TEMPERATURES = (0.5, 0.75, 1.0, 1.5, 2.0)

# Primary feature menus. None of these include a cohort indicator.
ORDINAL_FEATURES = {
    "h2": ["astra", "opus"],
    "h2_h3": ["astra", "opus", "h3_score", "h3_expected"],
    "h4": ["h4_astra", "h4_argon", "h4_opus"],
    "h2_h3_h4": ["astra", "opus", "h3_expected", "h4_astra", "h4_argon", "h4_opus"],
    "h2_h3_h4_struct": [
        "astra", "opus", "h3_expected", "h4_astra", "h4_argon", "h4_opus",
        "thm_ratio", "excess_thm_log", "ident_jaccard", "edit_similarity",
    ],
}
# Nested out-of-fold menu drops H3. Experiment 27's H3 prompt used labeled
# demonstrations from its training tasks, which cross the 50-task folds.
NESTED_ORDINAL_FEATURES = {
    "h2": ["astra", "opus"],
    "h4": ["h4_astra", "h4_argon", "h4_opus"],
    "h2_h4": ["astra", "opus", "h4_astra", "h4_argon", "h4_opus"],
    "h2_h4_struct": [
        "astra", "opus", "h4_astra", "h4_argon", "h4_opus",
        "thm_ratio", "excess_thm_log", "ident_jaccard", "edit_similarity",
    ],
}
LOGPOOL_SOURCES = {
    "h2_h3_h4": ["h2_prob", "h3_prob", "h4_astra_prob", "h4_argon_prob", "h4_opus_prob"],
    "h2_h4": ["h2_prob", "h4_astra_prob", "h4_argon_prob", "h4_opus_prob"],
    "h4": ["h4_astra_prob", "h4_argon_prob", "h4_opus_prob"],
}
F8_FEATURES = ["astra", "opus", "h3_score", "h3_expected"]


def smooth(p, eps=EPS):
    p = np.maximum(np.asarray(p, dtype=float), eps)
    return p / p.sum(axis=-1, keepdims=True)


def hist_from_ratings(ratings):
    return np.bincount(np.asarray(ratings, dtype=int), minlength=6) / len(ratings)


def rps(P, Q):
    """Per-row normalized ranked probability score. Lower is better."""
    pc = np.cumsum(P, axis=-1)[..., :5]
    qc = np.cumsum(Q, axis=-1)[..., :5]
    return np.mean((qc - pc) ** 2 + pc * (1.0 - pc), axis=-1)


def ce(P, Q):
    return -np.sum(np.where(P > 0, P * np.log(np.where(Q > 0, Q, 1.0)), 0.0), axis=-1)


def tvd(P, Q):
    return 0.5 * np.abs(P - Q).sum(axis=-1)


def marginal(C):
    c = np.asarray(C, dtype=float).sum(axis=0)
    return smooth(c / c.sum())


def corr_means(Q, P):
    qm = Q @ SCORES
    pm = P @ SCORES
    if np.ptp(qm) == 0 or np.ptp(pm) == 0:
        return float("nan"), float("nan")
    return float(stats.spearmanr(qm, pm).statistic), float(np.corrcoef(qm, pm)[0, 1])


def level_stats(Q, P):
    qm = Q @ SCORES
    pm = P @ SCORES
    return {
        "bias_judge_minus_human": float(qm.mean() - pm.mean()),
        "mean_judge": float(qm.mean()),
        "mean_human": float(pm.mean()),
        "mae": float(np.abs(qm - pm).mean()),
    }


class Ordinal:
    """P(r <= k) = sigmoid((theta_k - w·x) / T), thresholds increasing.

    Fit minimizes mean per-artifact cross-entropy or ranked probability score
    plus (alpha/2) ||w||^2. Optional mixture m with a constant forecast.
    const_mode 'pooled' uses one train marginal. const_mode 'per_set' uses the
    train marginal of the artifact's cohort (old or new); that uses cohort identity.
    """

    def __init__(self, cols, alpha=0.0, m=0.0, objective="ce", const_mode="pooled"):
        if objective not in OBJECTIVES:
            raise ValueError(objective)
        if const_mode not in ("pooled", "per_set"):
            raise ValueError(const_mode)
        self.cols = list(cols)
        self.alpha = float(alpha)
        self.m = float(m)
        self.objective = objective
        self.const_mode = const_mode

    def _x(self, D, idx):
        if not self.cols:
            return np.zeros((len(idx), 0))
        return np.column_stack([np.asarray(D[c], dtype=float)[idx] for c in self.cols])

    def _unpack(self, v):
        th = np.cumsum(np.concatenate([[v[0]], np.exp(v[1:5])]))
        return th, v[5:]

    def _q_ord(self, th, w, Xs, temperature):
        z = (th[None, :] - (Xs @ w)[:, None]) / float(temperature)
        # Clip only the overflow region. sigmoid(40) is 1 within 1e-17, so a
        # non-saturated head is unchanged at reported precision.
        F = 1.0 / (1.0 + np.exp(-np.clip(z, -40.0, 40.0)))
        F = np.concatenate([np.zeros((len(Xs), 1)), F, np.ones((len(Xs), 1))], axis=1)
        return np.diff(F, axis=1)

    def _const_rows(self, sets):
        if self.const_mode == "pooled":
            return np.repeat(self.const[None, :], len(sets), axis=0)
        return np.stack([self.const[s] for s in sets])

    def _mix(self, Qord, sets):
        return (1.0 - self.m) * Qord + self.m * self._const_rows(sets)

    def fit(self, D, idx):
        idx = np.asarray(idx, dtype=int)
        X = self._x(D, idx)
        self.mu = X.mean(axis=0)
        self.sd = X.std(axis=0) + 1e-9
        Xs = (X - self.mu) / self.sd
        P = D["P"][idx]
        sets = D["set"][idx]
        if self.const_mode == "pooled":
            self.const = marginal(D["C"][idx])
        else:
            self.const = {}
            for s in ("old", "new"):
                take = sets == s
                if not np.any(take):
                    raise RuntimeError(f"per-set constant has no {s} rows in the fit index")
                self.const[s] = marginal(D["C"][idx][take])
        c0 = self.const if self.const_mode == "pooled" else marginal(D["C"][idx])
        cdf = np.clip(np.cumsum(c0)[:5], 1e-4, 1 - 1e-4)
        th0 = np.log(cdf / (1.0 - cdf))
        v0 = np.concatenate([[th0[0]], np.log(np.maximum(np.diff(th0), 1e-3)), np.zeros(Xs.shape[1])])

        def loss(v):
            th, w = self._unpack(v)
            Q = smooth(self._mix(self._q_ord(th, w, Xs, 1.0), sets))
            score = ce(P, Q) if self.objective == "ce" else rps(P, Q)
            return float(score.mean() + 0.5 * self.alpha * (w @ w))

        result = optimize.minimize(loss, v0, method="L-BFGS-B", options={"maxiter": 250, "ftol": 1e-12})
        self.v = result.x
        self.train_loss = float(result.fun)
        self.optimizer_success = bool(result.success)
        return self

    def predict(self, D, idx, temperature=1.0):
        idx = np.asarray(idx, dtype=int)
        Xs = (self._x(D, idx) - self.mu) / self.sd
        th, w = self._unpack(self.v)
        Q = self._mix(self._q_ord(th, w, Xs, temperature), D["set"][idx])
        return smooth(Q)


class CohortSpecific:
    """One cumulative-logit head per cohort, same hyperparameters. Uses cohort identity."""

    def __init__(self, cols, alpha=0.0, m=0.0, objective="ce"):
        self.cols = list(cols)
        self.alpha = float(alpha)
        self.m = float(m)
        self.objective = objective
        self.const_mode = "cohort_specific"

    def fit(self, D, idx):
        idx = np.asarray(idx, dtype=int)
        self.models = {}
        for s in ("old", "new"):
            sub = idx[D["set"][idx] == s]
            if len(sub) == 0:
                raise RuntimeError(f"cohort-specific fit has no {s} rows")
            self.models[s] = Ordinal(self.cols, self.alpha, self.m, self.objective, "pooled").fit(D, sub)
        self.train_loss = float(np.mean([self.models[s].train_loss for s in ("old", "new")]))
        self.optimizer_success = all(self.models[s].optimizer_success for s in ("old", "new"))
        return self

    def predict(self, D, idx, temperature=1.0):
        idx = np.asarray(idx, dtype=int)
        out = np.zeros((len(idx), 6))
        sets = D["set"][idx]
        for s in ("old", "new"):
            take = np.where(sets == s)[0]
            if len(take) == 0:
                continue
            out[take] = self.models[s].predict(D, idx[take], temperature)
        return out


class LogPool:
    """Q proportional to a weighted geometric pool of cached probability vectors, then mixed with a constant.

    Weights are free (a negative weight down-weights a judge). L2 is on the weights.
    No cohort indicator.
    """

    def __init__(self, keys, alpha=0.0, m=0.0, objective="ce"):
        if objective not in OBJECTIVES:
            raise ValueError(objective)
        self.keys = list(keys)
        self.alpha = float(alpha)
        self.m = float(m)
        self.objective = objective
        self.const_mode = "pooled"

    def _logits(self, D, idx, w):
        L = np.zeros((len(idx), 6))
        for j, key in enumerate(self.keys):
            P = smooth(np.asarray(D[key], dtype=float)[idx], eps=1e-3)
            L += w[j] * np.log(P)
        return L

    def _q(self, logits, const, temperature):
        L = logits / float(temperature)
        L = L - L.max(axis=1, keepdims=True)
        Q = np.exp(L)
        Q = Q / Q.sum(axis=1, keepdims=True)
        return (1.0 - self.m) * Q + self.m * const

    def fit(self, D, idx):
        idx = np.asarray(idx, dtype=int)
        P = D["P"][idx]
        self.const = marginal(D["C"][idx])
        v0 = np.zeros(len(self.keys))

        def loss(v):
            Q = smooth(self._q(self._logits(D, idx, v), self.const, 1.0))
            score = ce(P, Q) if self.objective == "ce" else rps(P, Q)
            return float(score.mean() + 0.5 * self.alpha * (v @ v))

        result = optimize.minimize(loss, v0, method="L-BFGS-B", options={"maxiter": 250, "ftol": 1e-12})
        self.v = result.x
        self.train_loss = float(result.fun)
        self.optimizer_success = bool(result.success)
        return self

    def predict(self, D, idx, temperature=1.0):
        idx = np.asarray(idx, dtype=int)
        return smooth(self._q(self._logits(D, idx, self.v), self.const, temperature))


def fit_config(D, idx, spec):
    family = spec["family"]
    if family == "ordinal":
        return Ordinal(spec["features"], spec["alpha"], spec["mix"], spec["objective"], spec.get("const_mode", "pooled")).fit(D, idx)
    if family == "cohort_specific":
        return CohortSpecific(spec["features"], spec["alpha"], spec["mix"], spec["objective"]).fit(D, idx)
    if family == "logpool":
        return LogPool(spec["sources"], spec["alpha"], spec["mix"], spec["objective"]).fit(D, idx)
    raise ValueError(family)


def primary_eligible(spec):
    return spec["family"] in ("ordinal", "logpool") and spec.get("const_mode", "pooled") == "pooled" and "isnew" not in spec.get("features", [])


def iter_specs(ordinal_features, logpool_sources, include_set_aware):
    """Yield config dicts. Set-aware configs are marked and are not primary-eligible."""
    for name, cols in ordinal_features.items():
        for objective in OBJECTIVES:
            for alpha in ALPHAS:
                for mix in MIXES:
                    yield {
                        "family": "ordinal", "feature_set": name, "features": list(cols),
                        "sources": [], "objective": objective, "alpha": alpha, "mix": mix,
                        "const_mode": "pooled", "set_aware": False,
                    }
                    if include_set_aware:
                        yield {
                            "family": "ordinal", "feature_set": name + "_isnew", "features": list(cols) + ["isnew"],
                            "sources": [], "objective": objective, "alpha": alpha, "mix": mix,
                            "const_mode": "pooled", "set_aware": True,
                        }
                        yield {
                            "family": "ordinal", "feature_set": name + "_perset", "features": list(cols),
                            "sources": [], "objective": objective, "alpha": alpha, "mix": mix,
                            "const_mode": "per_set", "set_aware": True,
                        }
                        yield {
                            "family": "cohort_specific", "feature_set": name + "_by_cohort", "features": list(cols),
                            "sources": [], "objective": objective, "alpha": alpha, "mix": mix,
                            "const_mode": "cohort_specific", "set_aware": True,
                        }
    for name, keys in logpool_sources.items():
        for objective in OBJECTIVES:
            for alpha in ALPHAS:
                for mix in MIXES:
                    yield {
                        "family": "logpool", "feature_set": "logpool_" + name, "features": [],
                        "sources": list(keys), "objective": objective, "alpha": alpha, "mix": mix,
                        "const_mode": "pooled", "set_aware": False,
                    }


def better_val(a, b):
    """True if a should replace b. Lower validation ranked probability score, then cross-entropy, then smaller penalty, then temperature closer to 1."""
    if b is None:
        return True
    ka = (a["val_rps"], a["val_ce"], a["alpha"], abs(np.log(a["temperature"])), a["mix"], a["feature_set"], a["objective"])
    kb = (b["val_rps"], b["val_ce"], b["alpha"], abs(np.log(b["temperature"])), b["mix"], b["feature_set"], b["objective"])
    return ka < kb


def score_rows(P, Q):
    sp, pe = corr_means(Q, P)
    out = {"RPS": float(rps(P, Q).mean()), "CE": float(ce(P, Q).mean()), "TVD": float(tvd(P, Q).mean())}
    out.update(level_stats(Q, P))
    out["spearman"] = sp
    out["pearson"] = pe
    out["rps_floor"] = float(rps(P, P).mean())
    return out


def task_bootstrap(tasks, columns, draws=10000, seed=20261127):
    """Resample tasks with replacement. columns maps a name to a per-artifact vector. Returns point means and 95% percentile intervals."""
    tasks = np.asarray(tasks)
    ut = np.array(sorted(set(tasks.tolist())))
    groups = [np.where(tasks == t)[0] for t in ut]
    rng = np.random.default_rng(seed)
    point = {k: float(np.mean(v)) for k, v in columns.items()}
    acc = {k: np.empty(draws) for k in columns}
    n_tasks = len(ut)
    for b in range(draws):
        pick = rng.integers(0, n_tasks, n_tasks)
        idx = np.concatenate([groups[i] for i in pick])
        for k, v in columns.items():
            acc[k][b] = float(np.mean(v[idx]))
    ci = {k: [float(np.percentile(acc[k], 2.5)), float(np.percentile(acc[k], 97.5))] for k in columns}
    p_ge0 = {k: float((1 + np.sum(acc[k] >= 0.0)) / (draws + 1)) for k in columns}
    return point, ci, p_ge0, acc
