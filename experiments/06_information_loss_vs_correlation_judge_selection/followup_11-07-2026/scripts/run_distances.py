"""TLDR: Extend the completed cached selection study with W1 and Gaussian MMD squared."""
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.stats import rankdata, wasserstein_distance

BASE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(BASE / 'scripts'))
from metrics import histogram, smooth, per_item, summarize, choose, pearson
from run_cached import partitions, dump

GRID = np.arange(6) / 5
NEW = ('wasserstein1', 'mmd2')


def distances(p, q, sigma):
    kernel = np.exp(-((GRID[:, None] - GRID[None, :]) ** 2) / (2 * sigma**2))
    d = p - q
    return {'wasserstein1': np.abs(np.cumsum(d, axis=1)[:, :5]).sum(1) / 5,
            'mmd2': np.einsum('ni,ij,nj->n', d, kernel, d)}


def controls(sigma):
    p = np.eye(6)[[0, 0, 2]]
    q = np.eye(6)[[0, 5, 2]]
    q[2] = [0, .5, 0, .5, 0, 0]
    d = distances(p, q, sigma)
    assert d['wasserstein1'][0] == d['mmd2'][0] == 0
    assert np.isclose(d['wasserstein1'][1], 1)
    assert np.isclose(d['mmd2'][1], 2 * (1 - np.exp(-1 / (2 * sigma**2))))
    assert np.isclose(p[2] @ GRID, q[2] @ GRID) and all(v[2] > 0 for v in d.values())
    assert np.isclose(pearson(np.array([0., .2, .4]), np.array([.2, .4, .6])), 1)
    rng = np.random.default_rng(11072026)
    a, b = rng.dirichlet(np.ones(6), 20), rng.dirichlet(np.ones(6), 20)
    dd = distances(a, b, sigma)
    expected = [wasserstein_distance(GRID, GRID, x, y) for x, y in zip(a, b)]
    assert np.allclose(dd['wasserstein1'], expected, atol=1e-12)
    errors = []
    for i, (x, y) in enumerate(zip(a, b)):
        # Independent expectation form, not the quadratic-form implementation.
        value = sum((x[j]*x[k] + y[j]*y[k] - 2*x[j]*y[k]) *
                    np.exp(-(GRID[j]-GRID[k])**2/(2*sigma**2))
                    for j in range(6) for k in range(6))
        errors.append(abs(value - dd['mmd2'][i]))
    assert max(errors) < 1e-12
    return {'status': 'PASS', 'w1_endpoint': float(d['wasserstein1'][1]),
            'mmd2_endpoint': float(d['mmd2'][1]), 'independent_mmd_max_error': max(errors),
            'equal_mean_positive_distances': {k: float(v[2]) for k, v in d.items()}}


def interval(values):
    a = np.asarray(values)
    a = a[np.isfinite(a)]
    return {'lo': float(np.quantile(a, .025)) if len(a) else None,
            'hi': float(np.quantile(a, .975)) if len(a) else None,
            'valid_draws': len(a)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--data', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--private-out', required=True)
    ap.add_argument('--controls-only', action='store_true')
    args = ap.parse_args()
    here = Path(__file__).resolve().parents[1]
    cfg = json.loads((here / 'protocol.json').read_text())
    checks = controls(cfg['mmd_sigma'])
    if args.controls_only:
        print(json.dumps(checks)); return
    start = time.monotonic()
    out, private = Path(args.out), Path(args.private_out)
    assert not (out / 'results.json').exists(), 'Preserve completed evidence'
    data_path = Path(args.data)
    assert hashlib.sha256(data_path.read_bytes()).hexdigest() == cfg['dataset_sha256']
    data = json.loads(data_path.read_text())
    base_cfg = json.loads((BASE / 'protocol.json').read_text())
    previous = json.loads((BASE / 'results/results.json').read_text())['primary']
    names, rows = base_cfg['candidate_order'], data['rows']
    p = np.array([histogram(r['ratings']) for r in rows])
    q = np.array([smooth(np.array([histogram(r) for r in data['outputs'][name]]), cfg['epsilon'])
                  for name in names])
    items = [dict(per_item(p, v), **distances(p, v, cfg['mmd_sigma'])) for v in q]
    # Verify every real W1 observation independently, not just synthetic controls.
    for v, m in zip(q, items):
        assert np.allclose(m['wasserstein1'], [wasserstein_distance(GRID, GRID, x, y)
                                              for x, y in zip(p, v)], atol=1e-12)
    all_objectives = tuple(previous['matrix']) + NEW
    old_choices = {(s['seed'], s['fold'], s['objective']): s['candidate']
                   for s in previous['selections']}
    parts = partitions(rows, cfg['seeds'])
    forecasts = {o: [] for o in all_objectives}
    selections = []
    for si, (outer, _) in enumerate(parts):
        selected = {o: np.empty_like(p) for o in all_objectives}
        for fold in range(5):
            train, test = np.flatnonzero(outer != fold), np.flatnonzero(outer == fold)
            assert not ({rows[i]['family'] for i in train} & {rows[i]['family'] for i in test})
            for objective in all_objectives:
                if objective in NEW:
                    scores = [{objective: float(m[objective][train].mean())} for m in items]
                    j, fallback = choose(scores, objective, names)
                    assert not fallback
                    selections.append({'seed': cfg['seeds'][si], 'fold': fold,
                                       'objective': objective, 'candidate': names[j],
                                       'validation_artifacts': len(train), 'test_artifacts': len(test)})
                else:
                    j = names.index(old_choices[cfg['seeds'][si], fold, objective])
                selected[objective][test] = q[j, test]
        for objective in all_objectives:
            v = selected[objective]
            forecasts[objective].append(dict(per_item(p, v), **distances(p, v, cfg['mmd_sigma'])))

    def aggregate(ix):
        result = {}
        for o, ms in forecasts.items():
            vs = [summarize(m, ix) for m in ms]
            result[o] = {k: float(np.mean([v[k] for v in vs])) for k in vs[0]}
        return result

    matrix = aggregate(np.arange(len(rows)))
    for objective, metrics in previous['matrix'].items():
        for name, value in metrics.items():
            assert np.isclose(matrix[objective][name], value, rtol=1e-10, atol=1e-12), (objective, name)
    families = np.array([r['family'] for r in rows])
    unique = sorted(set(families))
    rng = np.random.default_rng(cfg['bootstrap_seed'])
    conditional = {o: {m: [] for m in matrix[o]} for o in NEW}
    refit = {o: [] for o in NEW}
    for b in range(cfg['bootstrap_draws']):
        draw = rng.choice(unique, len(unique), replace=True)
        ix = np.concatenate([np.flatnonzero(families == f) for f in draw])
        for o in NEW:
            vs = [summarize(m, ix) for m in forecasts[o]]
            for k in conditional[o]:
                conditional[o][k].append(float(np.mean([v[k] for v in vs])))
        per_seed = {o: [] for o in NEW}
        for outer, _ in parts:
            totals, count, valid = dict.fromkeys(NEW, 0.), 0, True
            for fold in range(5):
                train, test = ix[outer[ix] != fold], ix[outer[ix] == fold]
                if not len(test): continue
                if not len(train): valid = False; break
                human_rank = rankdata(items[0]['human_mean'][train])
                sp = [{'spearman': pearson(rankdata(m['judge_mean'][train]), human_rank)} for m in items]
                js, _ = choose(sp, 'spearman', names)
                for o in NEW:
                    j, _ = choose([{o: float(m[o][train].mean())} for m in items], o, names)
                    totals[o] += float((items[j][o][test] - items[js][o][test]).sum())
                count += len(test)
            for o in NEW:
                per_seed[o].append(totals[o] / count if valid and count else float('nan'))
        for o in NEW: refit[o].append(float(np.mean(per_seed[o])))
        if (b + 1) % 200 == 0:
            print(json.dumps({'bootstrap_completed': b+1}), flush=True)
    assert len(selections) == 50
    result = {'condition': cfg['version'], 'matrix': matrix, 'new_selections': selections,
              'new_selection_count': len(selections), 'reused_selection_count': len(old_choices),
              'artifacts': len(rows), 'tasks': len({r['task'] for r in rows}),
              'families': len(unique), 'expert_ratings': sum(len(r['ratings']) for r in rows),
              'conditional_intervals': {o: {k: interval(v) for k, v in d.items()} for o, d in conditional.items()},
              'selection_refit_contrasts': {o: {'estimate': matrix[o][o]-matrix['spearman'][o],
                                               **interval(refit[o]), 'p_value': None} for o in NEW},
              'controls': checks, 'old_metrics_reconstructed': True,
              'bootstrap_draws': cfg['bootstrap_draws'], 'elapsed_seconds': time.monotonic()-start,
              'dataset_sha256': cfg['dataset_sha256'],
              'protocol_sha256': hashlib.sha256((here/'protocol.json').read_bytes()).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'new_inference_calls': 0, 'provider_cost_usd': 0}
    dump(private / 'bootstrap.json', {'refit': refit, 'conditional': conditional})
    dump(out / 'results.json', result)
    print(json.dumps({'status': 'COMPLETE', 'new_selections': 50,
                      'contrasts': result['selection_refit_contrasts']}), flush=True)


if __name__ == '__main__':
    main()
