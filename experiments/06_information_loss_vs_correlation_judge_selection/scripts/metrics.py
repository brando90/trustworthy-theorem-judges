"""TLDR: Common six-category proper scores and paired expected-rating statistics."""
import numpy as np
from scipy.stats import rankdata, kendalltau

OBJECTIVES = ('ce', 'brier', 'rps', 'pearson', 'spearman', 'kendall', 'weighted_pmf', 'tvd')
HIGHER = {'pearson', 'spearman', 'kendall'}

def histogram(ratings):
    a = np.asarray(ratings, dtype=float)
    assert len(a) and np.all(np.isfinite(a)) and np.all(a == a.astype(int))
    assert np.all((0 <= a) & (a <= 5))
    return np.bincount(a.astype(int), minlength=6) / len(a)

def smooth(q, epsilon):
    q = np.asarray(q, dtype=float)
    assert q.shape[-1] == 6 and np.all(q >= 0) and np.allclose(q.sum(-1), 1)
    assert 0 < epsilon < 1/6
    return (1 - 6*epsilon)*q + epsilon

def per_item(p, q):
    assert p.shape == q.shape and p.shape[1] == 6
    assert np.allclose(p.sum(1), 1) and np.allclose(q.sum(1), 1)
    assert np.all(p >= 0) and np.all(q > 0)
    # Preserve mathematical ties despite different floating-point summation paths.
    mu_p = np.round(p @ (np.arange(6)/5), 12)
    mu_q = np.round(q @ (np.arange(6)/5), 12)
    entropy = -(p*np.log(np.maximum(p, 1e-300))).sum(1)
    ce = -(p*np.log(q)).sum(1)
    fp, fq = np.cumsum(p, axis=1)[:,:5], np.cumsum(q, axis=1)[:,:5]
    return {'ce':ce, 'kl':ce-entropy, 'entropy':entropy,
            'brier':1+(q*q).sum(1)-2*(p*q).sum(1),
            'rps':(fq*fq-2*fq*fp+fp).mean(1),
            'weighted_pmf':(p*(p-q)**2).sum(1), 'tvd':np.abs(p-q).sum(1)/2,
            'mae':np.abs(mu_q-mu_p), 'bias':mu_q-mu_p,
            'human_mean':mu_p, 'judge_mean':mu_q}

def pearson(x, y):
    x, y = np.asarray(x)-np.mean(x), np.asarray(y)-np.mean(y)
    den = np.sqrt((x@x)*(y@y))
    return float(x@y/den) if den > 1e-25 else float('nan')

def correlations(x, y):
    return {'pearson':pearson(x,y), 'spearman':pearson(rankdata(x),rankdata(y)),
            'kendall':float(kendalltau(x,y).statistic)}

def summarize(items, index):
    # Every task has exactly three artifacts, so artifact and task weighting coincide.
    out = {k:float(v[index].mean()) for k,v in items.items()}
    out.update(correlations(items['judge_mean'][index],items['human_mean'][index]))
    return out

def choose(scores, objective, order):
    # Undefined correlations are ineligible; deterministic fallback only if all undefined.
    direction = -1 if objective in HIGHER else 1
    valid = [j for j in range(len(order)) if np.isfinite(scores[j][objective])]
    if not valid: return 0, True
    return min(valid, key=lambda j:(direction*scores[j][objective], j)), False
