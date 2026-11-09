"""TLDR: Check mixture fits on synthetic recovery, exhaustive grids, negative correlations and degeneracies."""
import json
import numpy as np
from mixture_models import fit_mixture, predict_mixture, GRID


def _pmf(mean):
    mean = np.asarray(mean, dtype=float)
    q = np.zeros(mean.shape + (6,))
    q[..., 0], q[..., 5] = 1 - mean, mean
    return q


def _rho(q, p):
    u, v = q @ GRID, p @ GRID
    u, v = u - u.mean(), v - v.mean()
    return float(u @ v / (np.linalg.norm(u) * np.linalg.norm(v)))


def controls():
    rng = np.random.default_rng(20261108)
    q = rng.dirichlet(np.ones(6), size=(14, 3))
    truth = np.array([.2, .35, .45])
    p = predict_mixture(q, truth)
    recoveries = {}
    for objective in ['weighted_pmf', 'pearson']:
        w, rec = fit_mixture(q, p, objective)
        assert rec['success'], rec
        assert np.max(np.abs(w - truth)) < 1e-7, (objective, w)
        assert rec['training_weighted_pmf'] < 1e-15
        assert rec['training_pearson'] > 1 - 1e-12
        recoveries[objective] = float(np.max(np.abs(w - truth)))

    grids = []
    for trial in range(6):
        q = rng.dirichlet(np.ones(6), size=(12, 2))
        p = rng.dirichlet(np.ones(6), size=12)
        alpha = np.linspace(0, 1, 2001)
        forecasts = np.einsum('njr,aj->anr', q, np.column_stack([alpha, 1 - alpha]))
        losses = np.mean(np.sum(p[None] * (forecasts - p[None])**2, axis=2), axis=1)
        correlations = [_rho(f, p) for f in forecasts]
        for objective in ['weighted_pmf', 'pearson']:
            w, rec = fit_mixture(q, p, objective)
            assert rec['success'], rec
            if objective == 'weighted_pmf':
                gap = rec['training_weighted_pmf'] - float(losses.min())
                assert gap <= 1e-10
            else:
                gap = rec['training_pearson'] - max(correlations)
                assert gap >= -1e-10
            grids.append({'trial': trial, 'objective': objective, 'fit_minus_grid': gap})

    y = np.linspace(.1, .9, 15)
    q = _pmf(np.column_stack([.8 - .5*y + .03*np.sin(np.arange(15)),
                              .7 - .2*y + .04*np.cos(np.arange(15))]))
    p = _pmf(y)
    w, negative = fit_mixture(q, p, 'pearson')
    vertex = [_rho(q[:, j], p) for j in range(2)]
    assert negative['success'] and negative['status'] == 'optimal_nonpositive_vertex'
    assert abs(negative['training_pearson'] - max(vertex)) < 1e-12
    assert np.count_nonzero(w) == 1

    p = _pmf(np.array([0., 1., 0., 1.]))
    q = _pmf(np.column_stack([[.2, .2, .8, .8], [1., 0., 1., 0.]]))
    _, zero = fit_mixture(q, p, 'pearson')
    assert zero['success'] and abs(zero['training_pearson']) < 1e-12

    q0 = rng.dirichlet(np.ones(6), size=10)
    q1 = rng.dirichlet(np.ones(6), size=10)
    q = np.stack([q0, q0, q1], axis=1)
    duplicate_receipts = {}
    for objective in ['weighted_pmf', 'pearson']:
        w, rec = fit_mixture(q, q0, objective)
        assert rec['success'] and np.max(np.abs(w - [1, 0, 0])) < 1e-8, (objective, w, rec)
        duplicate_receipts[objective] = rec['support']

    constant = np.full((10, 3, 6), 1/6)
    _, all_constant = fit_mixture(constant, q0, 'pearson')
    assert all_constant['success'] and all_constant['undefined_correlation']
    _, target_constant = fit_mixture(q, np.full((10, 6), 1/6), 'pearson')
    assert target_constant['success'] and target_constant['undefined_correlation']
    # Constant expected ratings need not mean identical probability distributions.
    same_mean = np.zeros((8, 2, 6))
    same_mean[:, 0, [0, 5]] = .5
    same_mean[:, 1, [2, 3]] = .5
    _, same_mean_receipt = fit_mixture(same_mean, rng.dirichlet(np.ones(6), size=8), 'pearson')
    assert same_mean_receipt['undefined_correlation']

    # One constant candidate is excluded from the directional Pearson fit, explicitly fixing
    # a nonidentifiable affine degree of freedom rather than fitting it to test probabilities.
    q = np.stack([q0, np.full_like(q0, 1/6)], axis=1)
    w, mixed_constant = fit_mixture(q, q0, 'pearson')
    assert mixed_constant['success'] and np.max(np.abs(w - [1, 0])) < 1e-8

    return {'status': 'PASS', 'synthetic_only': True, 'seed': 20261108,
            'exact_recovery_weight_errors': recoveries, 'grid_comparisons': grids,
            'negative_case_pearson': negative['training_pearson'],
            'zero_case_pearson': zero['training_pearson'],
            'duplicate_tie_supports': duplicate_receipts,
            'constant_target_retained_undefined': target_constant['undefined_correlation'],
            'constant_forecasts_retained_undefined': all_constant['undefined_correlation'],
            'different_distributions_same_mean_undefined': same_mean_receipt['undefined_correlation'],
            'constant_candidate_excluded': mixed_constant['support']}


if __name__ == '__main__':
    print(json.dumps(controls(), sort_keys=True, indent=2, allow_nan=False))
