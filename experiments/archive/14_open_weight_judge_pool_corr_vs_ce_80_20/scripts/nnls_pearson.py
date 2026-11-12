"""Exact Pearson-maximizing simplex mixture for any number of judges (non-negative least squares on the cone).
TLDR: experiment 3's solver enumerates all 2^m active faces and caps m at 8; this does the same projection with scipy's NNLS (convex, global optimum), so a pool of 40+ judges works.
Same objective, same tie convention not guaranteed (ties are numerically measure-zero); checked against the enumeration solver at m=5 in check_nnls.py."""
import numpy as np
from scipy.optimize import nnls
GRID = np.arange(6, dtype=float)/5
CONST_TOL = 1e-12; CERT_TOL = 1e-8

def fit_pearson(q, p):
    n, m, _ = q.shape
    means, y = q @ GRID, p @ GRID
    a, b = means - means.mean(0), y - y.mean()
    norms, nb = np.linalg.norm(a, axis=0), float(np.linalg.norm(b))
    active = np.flatnonzero(norms > CONST_TOL)
    if nb <= CONST_TOL or len(active) == 0:
        return np.full(m, 1/m), {'status': 'undefined_target_or_all_constant_forecasts'}
    unit = a[:, active]/norms[active]
    prod = unit.T @ b
    if prod.max() <= 0:
        j = int(active[np.argmax(prod)]); return np.eye(m)[j], {'status': 'optimal_cone_projection'}
    c, _ = nnls(unit, b, maxiter=50*unit.shape[1])
    z = unit @ c
    grad = unit.T @ (z - b)
    dual = float(max(0.0, -grad.min())); comp = float(np.max(np.abs(c*grad))); orth = float(abs(z @ (b - z)))
    cert = max(dual/(1+nb), comp/(1+nb**2), orth/(1+nb**2))
    w = np.zeros(m); w[active] = c/norms[active]
    if w.sum() <= 0: return np.full(m, 1/m), {'status': 'certificate_failed'}
    w /= w.sum()
    return w, {'status': 'optimal_cone_projection' if cert <= CERT_TOL else 'certificate_failed', 'certificate_residual': cert}
