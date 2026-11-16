"""Matched historical probability mixtures; fitting uses only supplied training rows."""
import itertools
import time

import numpy as np

from vendor.mixture_models import fit_mixture, predict_mixture

GRID = np.arange(6) / 5


def histogram(values):
    values = np.asarray(values)
    if values.ndim != 1 or len(values) == 0 or not np.isfinite(values).all():
        raise ValueError('Expected a nonempty finite rating vector.')
    if np.any(values != values.astype(int)) or np.min(values) < 0 or np.max(values) > 5:
        raise ValueError('Ratings must be integers in 0..5.')
    return np.bincount(values.astype(int), minlength=6) / len(values)


def smooth(p, epsilon):
    """Same once-only floor/renormalization as the historical comparison."""
    p = np.maximum(np.asarray(p, dtype=float), epsilon)
    return p / p.sum(axis=-1, keepdims=True)


def rps(p, q):
    """Individual-rating proper RPS, averaged within artifact then over artifacts."""
    pc = np.cumsum(p, axis=-1)[..., :5]
    qc = np.cumsum(q, axis=-1)[..., :5]
    return float(np.mean((qc - pc)**2 + pc * (1 - pc)))


def fit_rps(q, p, cfg):
    """Convex quadratic on a simplex, exhaustively solve all nonempty faces."""
    q, p = np.asarray(q, float), np.asarray(p, float)
    n, m, k = q.shape
    assert k == 6 and p.shape == (n, 6) and n >= 2 and m <= 5
    assert np.isfinite(q).all() and np.isfinite(p).all()
    design = np.cumsum(q, axis=2)[:, :, :5].transpose(0, 2, 1).reshape(-1, m) / np.sqrt(5 * n)
    target = np.cumsum(p, axis=1)[:, :5].ravel() / np.sqrt(5 * n)
    gram, rhs = design.T @ design, design.T @ target
    candidates, rejected, solved = [], 0, 0
    for size in range(1, m + 1):
        for face in itertools.combinations(range(m), size):
            solved += 1
            ix = np.array(face)
            system = np.block([[gram[np.ix_(ix, ix)], np.ones((size, 1))],
                               [np.ones((1, size)), np.zeros((1, 1))]])
            b = np.r_[rhs[ix], 1.0]
            answer = np.linalg.lstsq(system, b, rcond=None)[0]
            if np.linalg.norm(system @ answer - b) > 1e-10 * (1 + np.linalg.norm(b)) or answer[:-1].min() < -1e-10:
                rejected += 1
                continue
            w = np.zeros(m)
            w[ix] = np.maximum(answer[:-1], 0)
            w /= w.sum()
            candidates.append((float(np.sum((design @ w - target)**2)), w, face))
    if not candidates:
        raise ArithmeticError('No feasible RPS face.')
    best = min(a[0] for a in candidates)
    tied = [a for a in candidates if a[0] <= best + cfg['tie_tolerance'] * (1 + abs(best))]
    def tie_key(a):
        support = tuple(np.flatnonzero(a[1] > 1e-10))
        return len(support), support, len(a[2]), a[2]
    value, weights, face = min(tied, key=tie_key)
    grad = 2 * design.T @ (design @ weights - target)
    gap = float(grad @ weights - grad.min())
    return weights, {
        'objective':'rps', 'algorithm':'finite_simplex_face_quadratic_v1',
        'success':gap <= cfg['certificate_tolerance'],
        'status':'optimal' if gap <= cfg['certificate_tolerance'] else 'certificate_failed',
        'simplex_frank_wolfe_gap':gap, 'empirical_cdf_squared_distance':value,
        'training_rps':rps(p, predict_mixture(q, weights)),
        'faces_total':2**m - 1, 'linear_solves':solved,
        'feasible_faces':len(candidates), 'rejected_faces':rejected,
        'selected_face':list(face), 'minimum_weight':float(weights.min()),
        'simplex_error':float(abs(weights.sum() - 1)),
    }


def predict(q, model):
    if model['kind'] == 'constant':
        return np.broadcast_to(model['constant'], (len(q), 6)).copy()
    mixture = predict_mixture(q, np.asarray(model['weights']))
    lam = model['shrinkage']
    return (1 - lam) * mixture + lam * np.asarray(model['constant'])


def train_select(qtrain, ptrain, qval, pval, cfg):
    """No test input or labels accepted here; candidates selected only by validation RPS."""
    constant = smooth(ptrain.mean(axis=0), cfg['epsilon'])
    models, records, searches = {}, [], {}
    for method in ['method2_pearson', 'method4_rps']:
        candidates = []
        for si, lam in enumerate(cfg['shrinkage_grid']):
            t0 = time.perf_counter()
            qt = (1 - lam) * qtrain + lam * constant
            if lam == 1:
                weights = np.ones(qtrain.shape[1]) / qtrain.shape[1]
                rec = {'objective':'shared_constant', 'success':True,
                       'status':'shared_baseline_no_objective_fit', 'faces_total':0,
                       'linear_solves':0, 'correlation_defined':False}
            elif method == 'method2_pearson':
                weights, rec = fit_mixture(qt, ptrain, 'pearson')
                rec['linear_solves'] = rec.get('feasible_faces', 0) + rec.get('rejected_faces', 0)
            else:
                weights, rec = fit_rps(qt, ptrain, cfg)
            rec = dict(rec, method=method, shrinkage=lam, grid_index=si,
                       elapsed_seconds=time.perf_counter() - t0)
            records.append(rec)
            if rec['linear_solves'] > cfg['max_faces_per_fit']:
                raise RuntimeError('Fixed per-fit computation budget exceeded.')
            model = {'kind':'mixture', 'weights':weights.tolist(),
                     'shrinkage':lam, 'constant':constant.tolist()}
            candidates.append({'model':model, 'validation_rps':rps(pval, predict(qval, model)),
                               'training_rps':rps(ptrain, predict(qtrain, model)),
                               'success':rec['success'], 'grid_index':si})
        # Failed numerical certificates invalidate the procedure, not merely a candidate.
        if not all(c['success'] for c in candidates):
            return None, records, {'failure':'training_certificate_failure', 'method':method}
        best = min(c['validation_rps'] for c in candidates)
        eligible = [c for c in candidates if c['validation_rps'] <= best + cfg['tie_tolerance']]
        chosen = min(eligible, key=lambda c:c['grid_index'])
        models[method] = chosen['model']
        searches[method] = candidates
    models['constant'] = {'kind':'constant', 'constant':constant.tolist()}
    models['equal_mixture'] = {'kind':'mixture', 'weights':(np.ones(qtrain.shape[1])/qtrain.shape[1]).tolist(),
                               'shrinkage':0.0, 'constant':constant.tolist()}
    baseline_scores = [rps(pval, qval[:, j]) for j in range(qtrain.shape[1])]
    j = min(range(len(baseline_scores)), key=lambda j:(baseline_scores[j], j))
    models['best_cached'] = {'kind':'mixture', 'weights':np.eye(qtrain.shape[1])[j].tolist(),
                             'shrinkage':0.0, 'constant':constant.tolist()}
    scores = {m:rps(pval, predict(qval, model)) for m,model in models.items()}
    best = min(scores.values())
    practical = next(m for m in cfg['overall_selection_order'] if scores[m] <= best + cfg['tie_tolerance'])
    models['validation_selected'] = models[practical]
    return models, records, {'searches':searches, 'validation_rps':scores,
                            'best_cached_candidate':cfg['candidate_order'][j],
                            'practical_selected_method':practical}
