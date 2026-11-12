"""TLDR: Fit weighted-PMF and globally optimal Pearson mixtures by finite active-face enumeration."""
import itertools
import numpy as np

GRID = np.arange(6, dtype=float) / 5
FEASIBILITY_TOL = 1e-10
SOLVE_TOL = 1e-10
CERTIFICATE_TOL = 1e-8
TIE_TOL = 1e-12
CONSTANT_NORM_TOL = 1e-12


def _inputs(q, p=None):
    q = np.asarray(q, dtype=float)
    assert q.ndim == 3 and q.shape[2] == 6 and 1 <= q.shape[1] <= 64  # experiment 14: cap raised from 8 (only the Pearson face enumeration needs it; replaced by nnls_pearson.py)
    assert len(q) >= 2 and np.isfinite(q).all()
    assert q.min() >= -FEASIBILITY_TOL
    assert np.max(np.abs(q.sum(axis=2) - 1)) <= FEASIBILITY_TOL
    if p is None:
        return q
    p = np.asarray(p, dtype=float)
    assert p.shape == (len(q), 6) and np.isfinite(p).all()
    assert p.min() >= -FEASIBILITY_TOL
    assert np.max(np.abs(p.sum(axis=1) - 1)) <= FEASIBILITY_TOL
    return q, p


def predict_mixture(q, weights):
    """Return the same simplex mixture at new items; no target-dependent remapping."""
    q = np.asarray(q, dtype=float)
    weights = np.asarray(weights, dtype=float)
    assert q.ndim == 3 and q.shape[2] == 6 and weights.shape == (q.shape[1],)
    assert np.isfinite(q).all() and np.isfinite(weights).all()
    assert weights.min() >= -FEASIBILITY_TOL
    assert abs(float(weights.sum()) - 1) <= FEASIBILITY_TOL
    return np.einsum('njr,j->nr', q, weights)


def _faces(m):
    for size in range(1, m + 1):
        yield from itertools.combinations(range(m), size)


def _tie_key(weights, face):
    support = tuple(np.flatnonzero(weights > FEASIBILITY_TOL).tolist())
    return len(support), support, len(face), face


def _best(candidates):
    value = min(item[0] for item in candidates)
    tied = [item for item in candidates if item[0] <= value + TIE_TOL * (1 + abs(value))]
    return min(tied, key=lambda item: _tie_key(item[1], item[2]))


def _base_receipt(objective, weights, q, p):
    forecast = predict_mixture(q, weights)
    mu, target = forecast @ GRID, p @ GRID
    u, v = mu - mu.mean(), target - target.mean()
    den = np.linalg.norm(u) * np.linalg.norm(v)
    rho = float(u @ v / den) if den > CONSTANT_NORM_TOL**2 and np.linalg.norm(u) > CONSTANT_NORM_TOL and np.linalg.norm(v) > CONSTANT_NORM_TOL else None
    return {
        'objective': objective,
        'algorithm': 'finite_active_face_enumeration_v1',
        'candidates': int(q.shape[1]),
        'faces_total': 2**q.shape[1] - 1,
        'simplex_error': float(abs(weights.sum() - 1)),
        'minimum_weight': float(weights.min()),
        'support': np.flatnonzero(weights > FEASIBILITY_TOL).tolist(),
        'training_weighted_pmf': float(np.mean(np.sum(p * (forecast - p)**2, axis=1))),
        'training_pearson': rho,
        'training_prediction_sd': float(mu.std()),
        'training_target_sd': float(target.std()),
        'undefined_correlation': rho is None,
        'tolerances': {'feasibility': FEASIBILITY_TOL, 'solve': SOLVE_TOL,
                       'certificate': CERTIFICATE_TOL, 'tie': TIE_TOL,
                       'constant_centered_norm': CONSTANT_NORM_TOL},
    }


def _weighted(q, p):
    n, m, _ = q.shape
    # F(w) = ||design @ w - target||^2, including the artifact mean.
    design = (np.sqrt(np.maximum(p, 0))[:, None, :] * q).transpose(0, 2, 1).reshape(-1, m) / np.sqrt(n)
    target = (np.sqrt(np.maximum(p, 0)) * p).ravel() / np.sqrt(n)
    gram, rhs = design.T @ design, design.T @ target
    candidates, rejected = [], 0
    for face in _faces(m):
        ix = np.array(face)
        k = len(face)
        system = np.block([[gram[np.ix_(ix, ix)], np.ones((k, 1))],
                           [np.ones((1, k)), np.zeros((1, 1))]])
        b = np.r_[rhs[ix], 1.0]
        solution = np.linalg.lstsq(system, b, rcond=None)[0]
        residual = np.linalg.norm(system @ solution - b)
        wf = solution[:-1]
        if residual > SOLVE_TOL * (1 + np.linalg.norm(b)) or wf.min() < -FEASIBILITY_TOL:
            rejected += 1
            continue
        weights = np.zeros(m)
        weights[ix] = np.maximum(wf, 0)
        weights /= weights.sum()
        loss = float(np.sum((design @ weights - target)**2))
        candidates.append((loss, weights, face))
    assert candidates, 'No feasible weighted-PMF face.'
    value, weights, face = _best(candidates)
    gradient = 2 * design.T @ (design @ weights - target)
    # For a differentiable convex objective on the simplex, this bounds F(w)-F*.
    gap = float(gradient @ weights - gradient.min())
    rec = _base_receipt('weighted_pmf', weights, q, p)
    rec.update(success=bool(gap <= CERTIFICATE_TOL), status='optimal' if gap <= CERTIFICATE_TOL else 'certificate_failed',
               objective_value=value, simplex_frank_wolfe_gap=gap,
               feasible_faces=len(candidates), rejected_faces=rejected,
               selected_face=list(face), identification='minimum support then lexicographic candidate index among numerical objective ties')
    return weights, rec


def _pearson(q, p):
    _, m, _ = q.shape
    means, y = q @ GRID, p @ GRID
    a, b = means - means.mean(axis=0), y - y.mean()
    norms, norm_b = np.linalg.norm(a, axis=0), float(np.linalg.norm(b))
    active = np.flatnonzero(norms > CONSTANT_NORM_TOL)
    if norm_b <= CONSTANT_NORM_TOL or len(active) == 0:
        weights = np.full(m, 1 / m)
        rec = _base_receipt('pearson', weights, q, p)
        rec.update(success=True, status='undefined_target_or_all_constant_forecasts',
                   identification='uniform simplex weights; undefined correlation is retained, never replaced by zero',
                   feasible_faces=0, rejected_faces=0, optimal_correlation=None)
        return weights, rec
    # Column normalization preserves the cone and improves the least-squares conditioning.
    unit = a[:, active] / norms[active]
    products = unit.T @ b
    single_correlations = products / norm_b
    if np.max(products) <= 0:
        # For nonpositive numerators, the triangle inequality bounds every mixture by its best vertex.
        best = float(single_correlations.max())
        eligible = np.flatnonzero(single_correlations >= best - TIE_TOL)
        j = int(active[eligible[0]])
        weights = np.eye(m)[j]
        rec = _base_receipt('pearson', weights, q, p)
        rec.update(success=True, status='optimal_nonpositive_vertex',
                   identification='lowest candidate index among numerically tied best nonconstant vertices',
                   feasible_faces=len(active), rejected_faces=0, optimal_correlation=best,
                   candidate_correlations=single_correlations.tolist(), active_candidates=active.tolist())
        return weights, rec
    # The cone projection has an independent-generator representation, so enumerating all
    # nonnegative least-squares faces includes an optimum even with duplicate columns.
    candidates, rejected = [], 0
    for face_local in _faces(len(active)):
        ix = np.array(face_local)
        af = unit[:, ix]
        coefficient = np.linalg.lstsq(af, b, rcond=None)[0]
        if coefficient.min() < -FEASIBILITY_TOL:
            rejected += 1
            continue
        coefficient = np.maximum(coefficient, 0)
        if coefficient.sum() <= 0:
            rejected += 1
            continue
        full = np.zeros(len(active))
        full[ix] = coefficient
        z = unit @ full
        loss = float(np.sum((z - b)**2))
        weights = np.zeros(m)
        weights[active] = full / norms[active]
        weights /= weights.sum()
        candidates.append((loss, weights, tuple(active[ix].tolist()), full, z))
    assert candidates, 'Positive correlation exists but no positive cone face was found.'
    value = min(item[0] for item in candidates)
    tied = [item for item in candidates if item[0] <= value + TIE_TOL * (1 + abs(value))]
    chosen = min(tied, key=lambda item: _tie_key(item[1], item[2]))
    _, weights, face, coefficient, z = chosen
    gradient = unit.T @ (z - b)
    dual_violation = float(max(0.0, -gradient.min()))
    complementarity = float(np.max(np.abs(coefficient * gradient)))
    orthogonality = float(abs(z @ (b - z)))
    optimum = float(np.linalg.norm(z) / norm_b)
    rec = _base_receipt('pearson', weights, q, p)
    identity_error = float(abs(rec['training_pearson'] - optimum)) if rec['training_pearson'] is not None else float('inf')
    certificate = max(dual_violation / (1 + norm_b), complementarity / (1 + norm_b**2),
                      orthogonality / (1 + norm_b**2), identity_error)
    rec.update(success=bool(certificate <= CERTIFICATE_TOL),
               status='optimal_cone_projection' if certificate <= CERTIFICATE_TOL else 'certificate_failed',
               identification='minimum support then lexicographic candidate index among numerical cone-projection ties; normalize nonnegative coefficients to sum one',
               optimal_correlation=optimum, cone_residual_squared=value,
               cone_dual_violation=dual_violation, cone_complementarity=complementarity,
               cone_orthogonality=orthogonality, correlation_identity_error=identity_error,
               certificate_residual=certificate, feasible_faces=len(candidates),
               rejected_faces=rejected, selected_face=list(face), active_candidates=active.tolist())
    return weights, rec


def fit_mixture(qtrain, p, objective):
    """Fit one global simplex weight vector using only this call's training rows."""
    qtrain, p = _inputs(qtrain, p)
    if objective == 'weighted_pmf':
        return _weighted(qtrain, p)
    if objective == 'pearson':
        return _pearson(qtrain, p)
    raise ValueError('Unsupported objective: ' + str(objective))
