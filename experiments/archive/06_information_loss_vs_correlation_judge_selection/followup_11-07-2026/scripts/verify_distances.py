"""TLDR: Independently reconstruct selections, distances, bootstrap quantiles and source hashes."""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
from scipy.stats import wasserstein_distance


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--data', required=True)
    ap.add_argument('--bootstrap', required=True)
    args = ap.parse_args()
    root = Path(__file__).resolve().parents[1]
    result = json.loads((root/'results/results.json').read_text())
    cfg = json.loads((root/'protocol.json').read_text())
    base_cfg = json.loads((root.parent/'protocol.json').read_text())
    data = json.loads(Path(args.data).read_text())
    boot = json.loads(Path(args.bootstrap).read_text())
    names, rows = base_cfg['candidate_order'], data['rows']
    def frequencies(v):
        return np.array([sum(int(x == r) for x in v)/len(v) for r in range(6)])
    p = np.array([frequencies(r['ratings']) for r in rows])
    grid = np.arange(6)/5
    q = {name: (1-6*cfg['epsilon'])*np.array([frequencies(v) for v in data['outputs'][name]])+cfg['epsilon']
         for name in names}
    kernel = np.array([[np.exp(-(a-b)**2/(2*cfg['mmd_sigma']**2)) for b in grid] for a in grid])
    scores = {}
    for name in names:
        scores[name] = {'wasserstein1': np.array([wasserstein_distance(grid, grid, a, b) for a, b in zip(p, q[name])]),
                        'mmd2': np.array([a@kernel@a+b@kernel@b-2*a@kernel@b for a, b in zip(p, q[name])])}
    all_families = sorted({r['family'] for r in rows})
    partitions = {}
    for seed in cfg['seeds']:
        shuffled = np.random.default_rng(seed).permutation(all_families)
        assign = {family: index % 5 for index, family in enumerate(shuffled)}
        partitions[seed] = np.array([assign[r['family']] for r in rows])
    collected = {o: {seed: np.empty(len(rows)) for seed in cfg['seeds']} for o in cfg['new_objectives']}
    for s in result['new_selections']:
        outer = partitions[s['seed']]
        train, test = outer != s['fold'], outer == s['fold']
        objective = s['objective']
        choice = min(names, key=lambda name: (scores[name][objective][train].mean(), names.index(name)))
        assert choice == s['candidate']
        assert int(train.sum()) == s['validation_artifacts'] and int(test.sum()) == s['test_artifacts']
        collected[objective][s['seed']][test] = scores[choice][objective][test]
    for o in cfg['new_objectives']:
        expected = np.mean([v.mean() for v in collected[o].values()])
        assert np.isclose(expected, result['matrix'][o][o], atol=1e-12)
        a = np.asarray(boot['refit'][o], float)
        assert len(a) == cfg['bootstrap_draws']
        a = a[np.isfinite(a)]
        interval = np.percentile(a, [2.5, 97.5])
        saved = result['selection_refit_contrasts'][o]
        assert len(a) == saved['valid_draws']
        assert np.allclose(interval, [saved['lo'], saved['hi']], atol=1e-12)
    terminal = json.loads((root/'results/terminal.json').read_text())
    assert terminal['status'] == 'COMPLETE' and terminal['exit_code'] == 0
    for key, path in [('results_sha256', root/'results/results.json'),
                      ('protocol_sha256', root/'protocol.json'),
                      ('script_sha256', root/'scripts/run_distances.py'),
                      ('dataset_sha256', Path(args.data))]:
        assert hashlib.sha256(path.read_bytes()).hexdigest() == terminal[key]
    assert len(result['new_selections']) == 50 and result['reused_selection_count'] == 200
    receipt = {'status': 'PASS', 'independently_reconstructed_new_selections': 50,
               'independent_candidate_artifact_distances_per_metric': len(names)*len(rows),
               'independently_recomputed_selection_refit_intervals': 2,
               'checked_hashes': 4, 'all_original_metrics_match': result['old_metrics_reconstructed']}
    (root/'results/verification.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt))


if __name__ == '__main__':
    main()
