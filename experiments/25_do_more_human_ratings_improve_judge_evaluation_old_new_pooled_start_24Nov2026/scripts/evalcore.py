"""Metrics and task-bootstrap for the pooled old/new evaluation (exp 25). Dated 11-24-2026. CPU only, no model calls.

Definitions follow experiment 22: judge distribution = histogram of the repeat scores over 0..5 floored at eps once and
renormalised; human distribution = empirical histogram of the artifact's ratings; RPS is the 5-threshold mean of
(Qc-Pc)^2 + Pc(1-Pc); every metric is averaged per artifact and then with equal weight over artifacts.
"""
import numpy as np
from scipy import stats

EPS = 1e-6


def hist(vals):
    return np.bincount(np.asarray(vals, dtype=int), minlength=6) / len(vals)


def smooth(p, eps=EPS):
    p = np.maximum(np.asarray(p, dtype=float), eps)
    return p / p.sum(axis=-1, keepdims=True)


def rps_art(P, Q):
    pc = np.cumsum(P, -1)[..., :5]
    qc = np.cumsum(Q, -1)[..., :5]
    return np.mean((qc - pc) ** 2 + pc * (1 - pc), -1)


def floor_art(P):
    """Irreducible part of RPS against the empirical human distribution: mean Pc(1-Pc) (rater disagreement)."""
    pc = np.cumsum(P, -1)[..., :5]
    return np.mean(pc * (1 - pc), -1)


def ce_art(P, Q):
    return -np.sum(np.where(P > 0, P * np.log(np.where(Q > 0, Q, 1)), 0.0), -1)


def tvd_art(P, Q):
    return 0.5 * np.abs(P - Q).sum(-1)


def per_artifact(P, Q):
    return {"RPS": rps_art(P, Q), "CE": ce_art(P, Q), "TVD": tvd_art(P, Q)}


def loto_constant(P_counts, tasks):
    """Constant baseline: pooled human marginal of all OTHER tasks (leave-one-task-out), per artifact."""
    tasks = np.asarray(tasks)
    Q = np.zeros_like(P_counts)
    for t in set(tasks):
        m = tasks == t
        c = P_counts[~m].sum(0)
        Q[m] = smooth(c / c.sum())
    return Q


def _pearson(a, b):
    a = a - a.mean(); b = b - b.mean()
    d = np.sqrt((a * a).sum() * (b * b).sum())
    return float((a * b).sum() / d)


def corr_pair(j, h):
    """(Spearman, Pearson) of two score vectors; nan when either is constant."""
    if np.ptp(j) == 0 or np.ptp(h) == 0:
        return np.nan, np.nan
    return _pearson(stats.rankdata(j), stats.rankdata(h)), _pearson(j, h)


def boot_tasks(tasks, fn, draws=10000, seed=20261124):
    """fn(index_array) -> dict of metric -> value. Returns point estimate and 95% percentile interval from task resampling."""
    tasks = np.asarray(tasks)
    ut = sorted(set(tasks))
    idx_by = {t: np.where(tasks == t)[0] for t in ut}
    rng = np.random.default_rng(seed)
    point = fn(np.arange(len(tasks)))
    out = {k: [] for k in point}
    for _ in range(draws):
        pick = rng.integers(0, len(ut), len(ut))
        idx = np.concatenate([idx_by[ut[i]] for i in pick])
        r = fn(idx)
        for k, v in r.items():
            out[k].append(v)
    ci = {k: (float(np.nanpercentile(v, 2.5)), float(np.nanpercentile(v, 97.5))) for k, v in out.items()}
    return point, ci
