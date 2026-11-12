"""Toy: a flexible judge fitted by Pearson vs by cross-entropy (CE) vs RPS on synthetic ratings 0..5.

Humans' rating distribution p*(x) (beta-binomial on 0..5) depends nonlinearly on a task feature x in [-1,1].
Every judge has the same function class (softmax of a cosine-basis linear map, 13 features x 6 logits)
or, for the Pearson+head variant, a scalar score followed by a calibrated ordinal head. Only the objective differs.
Pure numpy/scipy, CPU. Data: n train tasks, k=3 raters each; test: fresh tasks scored against the TRUE p*.
"""
import numpy as np
from scipy.optimize import minimize
from scipy.special import gammaln, softmax

GRID = np.arange(6.0)
J = 6                       # cosine/sine harmonics -> D = 2J+1 = 13 features
RIDGE_C = 1.0               # ridge = RIDGE_C/n on the summed objective (decays with n -> consistent)
FLOOR = 1e-6                # CE floor, as in the repo

def phi(x, J=J):
    cols = [np.ones_like(x)]
    for j in range(1, J + 1):
        cols += [np.cos(np.pi * j * x), np.sin(np.pi * j * x)]
    return np.stack(cols, 1)

def betabinom(mu, kappa):
    """Beta-binomial(5, a=mu*kappa, b=(1-mu)*kappa): mean 5*mu for every kappa; kappa small -> U-shaped."""
    a, b = mu * kappa, (1 - mu) * kappa
    k = GRID[None]
    lg = (gammaln(6) - gammaln(k + 1) - gammaln(6 - k) + gammaln(k + a[:, None]) + gammaln(5 - k + b[:, None])
          - gammaln(5 + (a + b)[:, None]) + gammaln((a + b)[:, None]) - gammaln(a[:, None]) - gammaln(b[:, None]))
    return np.exp(lg)

def truth(x, scenario):
    kappa = np.exp(1.5 + 2.2 * np.cos(2 * np.pi * 0.75 * x))      # spread varies nonlinearly with x
    if scenario == 'A':     # same mean (almost): mean 2.1..2.9 on a small linear drift, spread varies a lot
        mu = 0.5 + 0.08 * x
    else:                   # 'B': human mean is a monotone nonlinear (convex) function of x
        mu = 0.1 + 0.8 * ((x + 1) / 2) ** 2
    return betabinom(mu, kappa)

# ---- losses and analytic gradients wrt logits Z (m x 6); P = target histogram, Q = softmax(Z)
def ce_loss_grad(Z, P):
    Q = np.clip(softmax(Z, 1), FLOOR, None); Q /= Q.sum(1, keepdims=True)
    L = -(P * np.log(Q)).sum(1)
    return L, Q - P                                   # dL/dZ (P sums to 1)

def rps_loss_grad(Z, P):
    Q = softmax(Z, 1)
    d = np.cumsum(Q, 1)[:, :5] - np.cumsum(P, 1)[:, :5]
    L = (d ** 2).mean(1)
    g = np.zeros_like(Q)                            # dL/dq_j = (2/5) sum_{k>=j, k<5} d_k
    g[:, :5] = (2 / 5) * np.cumsum(d[:, ::-1], 1)[:, ::-1]
    return L, Q * (g - (Q * g).sum(1, keepdims=True))

def fit(Phi, P, kind, n, W0, c=RIDGE_C):
    """Minimise mean objective + (c/n)*||W||^2 (= summed objective + c*||W||^2); returns W (D x 6)."""
    D = Phi.shape[1]; lam = c / n
    def f(w):
        W = w.reshape(D, 6); Z = Phi @ W
        if kind == 'ce':
            L, G = ce_loss_grad(Z, P); obj = L.mean(); dZ = G / len(P)
        elif kind == 'rps':
            L, G = rps_loss_grad(Z, P); obj = L.mean(); dZ = G / len(P)
        else:                                       # 'pearson': minimise -corr(pred mean, human mean)
            Q = softmax(Z, 1); mu = Q @ GRID; h = P @ GRID
            a, b = mu - mu.mean(), h - h.mean(); na, nb = np.linalg.norm(a) + 1e-12, np.linalg.norm(b) + 1e-12
            r = a @ b / (na * nb); obj = -r
            dmu = -(b / nb - r * a / na) / na
            dZ = Q * (GRID[None] - mu[:, None]) * dmu[:, None]
        return obj + lam * (W ** 2).sum(), (Phi.T @ dZ + 2 * lam * W).ravel()
    res = minimize(f, W0.ravel(), jac=True, method='L-BFGS-B', options={'maxiter': 400, 'maxfun': 600})
    return res.x.reshape(D, 6)

def marginal_W0(Phi, P, seed=0):
    """Start at the constant (train-marginal) forecast plus a tiny seeded perturbation (breaks the constant-score tie
    that makes Pearson undefined; the Pearson fit's spread shape is whatever this start plus the ridge leave)."""
    W0 = 0.01 * np.random.default_rng(seed).normal(size=(Phi.shape[1], 6)); W0[0] += np.log(np.clip(P.mean(0), 1e-3, None)); return W0

def metrics(Q, Ptrue, x):
    Q = np.clip(Q, FLOOR, None); Q = Q / Q.sum(1, keepdims=True)
    pc, qc = np.cumsum(Ptrue, 1)[:, :5], np.cumsum(Q, 1)[:, :5]
    rps_ex = ((qc - pc) ** 2).mean(1)                       # RPS minus the best judge's RPS (best = truth)
    rps = rps_ex + (pc * (1 - pc)).mean(1)                  # repo RPS vs the true distribution
    kl = (Ptrue * (np.log(np.clip(Ptrue, 1e-12, None)) - np.log(Q))).sum(1)
    ce = kl - (Ptrue * np.log(np.clip(Ptrue, 1e-12, None))).sum(1)
    tvd = 0.5 * np.abs(Q - Ptrue).sum(1)
    mu, hm = Q @ GRID, Ptrue @ GRID
    from scipy.stats import spearmanr
    pear = np.corrcoef(mu, hm)[0, 1] if mu.std() > 1e-12 else np.nan
    sp = spearmanr(mu, hm)[0] if mu.std() > 1e-12 else np.nan
    return dict(rps=rps.mean(), rps_excess=rps_ex.mean(), ce=ce.mean(), ce_excess=kl.mean(), tvd=tvd.mean(),
                spearman=sp, pearson=pear)

FITS = ['ce', 'rps', 'pearson', 'pearson_head']

def run_one(args):
    scenario, n, seed, k, ntest = args
    rng = np.random.default_rng(1000003 * seed + 7919 * n + (scenario == 'B'))
    x = rng.uniform(-1, 1, n); Ptr = truth(x, scenario)
    cnt = np.array([rng.multinomial(k, p) for p in Ptr]); P = cnt / k          # k raters per task
    Phi = phi(x); W0 = marginal_W0(Phi, P, seed)
    xt = rng.uniform(-1, 1, ntest); Pt = truth(xt, scenario); Phit = phi(xt)
    out = {}
    Ws = {kind: fit(Phi, P, kind, n, W0) for kind in ['ce', 'rps', 'pearson']}
    for kind, W in Ws.items():
        out[kind] = metrics(softmax(Phit @ W, 1), Pt, xt)
    # Pearson fit, then a calibrated ordinal head on the scalar score (fit by CE on the same train tasks)
    s_tr = softmax(Phi @ Ws['pearson'], 1) @ GRID; s_te = softmax(Phit @ Ws['pearson'], 1) @ GRID
    m, sd = s_tr.mean(), s_tr.std() + 1e-9
    H = np.stack([np.ones(n), (s_tr - m) / sd], 1); Ht = np.stack([np.ones(ntest), (s_te - m) / sd], 1)
    Wh = fit(H, P, 'ce', n, marginal_W0(H, P, seed))
    out['pearson_head'] = metrics(softmax(Ht @ Wh, 1), Pt, xt)
    return scenario, n, seed, out

def population_limit(scenario, kind, ngrid=4000):
    """n -> infinity: fit on a dense x grid with the TRUE distributions (no sampling noise, no ridge)."""
    x = np.linspace(-1, 1, ngrid); P = truth(x, scenario); Phi = phi(x); W0 = marginal_W0(Phi, P)
    if kind == 'pearson_head':
        Wp = fit(Phi, P, 'pearson', ngrid * 1e6, W0); s = softmax(Phi @ Wp, 1) @ GRID
        H = np.stack([np.ones(ngrid), (s - s.mean()) / s.std()], 1); W = fit(H, P, 'ce', ngrid * 1e6, marginal_W0(H, P)); Z = H @ W
    else:
        W = fit(Phi, P, kind, ngrid * 1e6, W0); Z = Phi @ W
    return metrics(softmax(Z, 1), P, x)
