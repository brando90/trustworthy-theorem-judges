"""Shared pieces of experiment 12: data loading, task-grouped 20/5 splits, scoring.
TLDR: one place for the split rule (so the agents and the repeated run use the same fixed split) and the per-artifact metrics."""
import sys, json
from pathlib import Path
import numpy as np
from scipy.stats import rankdata
HERE = Path(__file__).parent
sys.path.insert(0, str(HERE/'exp10_scripts')); sys.path.insert(0, str(HERE/'vendor_exp03'))
from models import histogram, smooth  # noqa
EPS = 1e-6
GRID = np.arange(6)/5
FIXED_SEED = 1210          # fixed before any fitting: split 1210 of the 20/5 rule below
REPEAT_SEED0 = 20261210    # repeated splits use seeds REPEAT_SEED0 + s

def load(path):
    d = json.load(open(path)); rows = d['rows']; order = d['candidate_order']
    p = np.array([histogram(r['ratings']) for r in rows])
    q = np.stack([smooth(np.array([histogram(x) for x in d['outputs'][n]]), EPS) for n in order], axis=1)
    tasks = np.array([r['task'] for r in rows])
    return d, rows, order, p, q, tasks

def split_tasks(tasks, seed, n_test=5):
    """20 train / 5 test tasks, grouped by task; returns (train_idx, test_idx) over artifacts."""
    ut = sorted(set(tasks)); rng = np.random.default_rng(seed)
    test_t = set(rng.permutation(ut)[:n_test].tolist())
    te = np.array([t in test_t for t in tasks])
    return np.flatnonzero(~te), np.flatnonzero(te)

def ce(P, Q): return -np.sum(P*np.log(Q), axis=-1)
def rps(P, Q):
    pc = np.cumsum(P, -1)[:, :5]; qc = np.cumsum(Q, -1)[:, :5]
    return np.mean((qc-pc)**2 + pc*(1-pc), axis=-1)
def tvd(P, Q): return 0.5*np.abs(P-Q).sum(-1)

def pearson(x, y):
    a, b = x-x.mean(), y-y.mean(); na, nb = np.linalg.norm(a), np.linalg.norm(b)
    return float(a@b/(na*nb)) if na > 1e-12 and nb > 1e-12 else float('nan')
def spearman(x, y): return pearson(rankdata(x), rankdata(y))

def score(P, Q):
    """Per-artifact CE/RPS/TVD arrays and the test-set Pearson/Spearman of judge mean vs human mean."""
    mu, hm = Q@GRID, P@GRID
    return {'ce': ce(P, Q), 'rps': rps(P, Q), 'tvd': tvd(P, Q), 'pearson': pearson(mu, hm), 'spearman': spearman(mu, hm)}
