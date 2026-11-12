"""Equal-artifact ordinal proper losses and empirical-distribution diagnostics."""
import numpy as np
from scipy.stats import rankdata, kendalltau

GRID = np.arange(6)/5


def corr(x, y):
    x, y = np.asarray(x, float), np.asarray(y, float)
    a, b = x - x.mean(), y - y.mean()
    if np.linalg.norm(a) <= 1e-12 or np.linalg.norm(b) <= 1e-12:
        return None
    return float(a @ b / (np.linalg.norm(a) * np.linalg.norm(b)))


def per_item(p, q):
    p, q = np.asarray(p, float), np.asarray(q, float)
    assert p.shape == q.shape and p.ndim == 2 and p.shape[1] == 6
    assert np.isfinite(p).all() and np.isfinite(q).all()
    assert np.min(q) > 0 and np.min(p) >= 0
    assert np.allclose(q.sum(1),1,atol=1e-12) and np.allclose(p.sum(1),1,atol=1e-12)
    P, Q = np.cumsum(p,1)[:,:5], np.cumsum(q,1)[:,:5]
    mu, target = q @ GRID, p @ GRID
    disagreement = np.mean(P * (1 - P),axis=1)
    distance = np.mean((Q - P)**2,axis=1)
    entropy = -np.sum(p * np.log(np.maximum(p,1e-300)),axis=1)
    ce = -np.sum(p*np.log(q),axis=1)
    return {'rps':distance + disagreement, 'ce':ce,
            'tvd':np.abs(q-p).sum(1)/2,
            'brier':1 + np.sum(q*q - 2*p*q,axis=1),
            'kl':ce-entropy, 'weighted_pmf':np.sum(p*(p-q)**2,axis=1),
            'empirical_cdf_squared_distance':distance,
            'empirical_disagreement':disagreement, 'entropy':entropy,
            'mse':(mu-target)**2, 'mae':np.abs(mu-target), 'bias':mu-target,
            'judge_mean':mu, 'human_mean':target}


def summarize(p, q):
    vals=per_item(p,q)
    out={k:float(v.mean()) for k,v in vals.items()}
    mu,target=vals['judge_mean'],vals['human_mean']
    out['nrmse']=float(np.sqrt(out['mse']))
    out['root_mean_cdf_distance']=float(np.sqrt(out['empirical_cdf_squared_distance']))
    out['pearson']=corr(mu,target)
    out['spearman']=corr(rankdata(mu),rankdata(target))
    out['kendall_tau_b']=float(kendalltau(mu,target).statistic) if out['pearson'] is not None else None
    out['judge_sd']=float(mu.std())
    out['human_sd']=float(target.std())
    return out


def interval(values):
    vals=np.asarray([np.nan if v is None else v for v in values],float)
    valid=vals[np.isfinite(vals)]
    return {'low':float(np.quantile(valid,.025)) if len(valid) else None,
            'high':float(np.quantile(valid,.975)) if len(valid) else None,
            'valid_draws':len(valid),'undefined_draws':len(vals)-len(valid),'p_value':None}
