#!/usr/bin/env python3
"""TLDR: Reproduce aggregate binary forecasting results from hash-pinned private receipts without publishing per-artifact data."""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import platform
import re
import subprocess
from pathlib import Path

import numpy as np
import scipy
from scipy.optimize import minimize
from scipy.special import expit
from scipy.stats import kendalltau, rankdata

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT.parents[1]
E117 = 'experiments/117_fsc_judge_vs_prover_entailment_correlation_75_human_rated_items/'
E140 = 'experiments/140_entailment_check_vs_theorem_coverage_tiny256_10-31-2026/'
E142 = 'experiments/142_entailment_lean_proofs_all_tiny256_10-31-2026/'
E145 = 'experiments/145_entailment_vacuity_axiom_check_tiny256_11-01-2026/'
E168 = 'experiments/168_harsh_prover_pd_pf_detection_controls_tiny256_11-04-2026/'
SOURCES = [
    E140 + 'manifest_tiny256.json', E145 + 'results/per_run.csv',
    E117 + 'PROTOCOL_phaseA_t2.md', E117 + 'expt_v1/scripts/VB117Harness.lean',
    E117 + 'expt_v1/results/g2v2_t2check_goals.csv',
    E140 + 'PROTOCOL.md', E140 + 'LEAN_PROTOCOL.md', E142 + 'README.md',
    E145 + 'README.md', E145 + 'lean/GoldChkLib.lean', E145 + 'lean/WitLib.lean',
    E145 + 'lean/AxLib.lean', E145 + 'scripts/gold_name_check.py',
    E168 + 'README.md', E168 + 'attacks/summary.json',
    E168 + 'scripts/attacks_check_candidate_patched.py',
    E168 + 'scripts/prover_pi_runner.py',
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dump(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + '\n')


def read_sources(repo, revision):
    blobs, provenance = {}, []
    for name in SOURCES:
        raw = subprocess.check_output(['git', '-C', str(repo), 'show', f'{revision}:{name}'])
        blobs[name] = raw
        provenance.append({'path': name, 'sha256': sha(raw), 'bytes': len(raw)})
    return blobs, provenance


def load_rows(blobs):
    labels = list(csv.DictReader(io.StringIO(blobs[E145 + 'results/per_run.csv'].decode())))
    scores = json.loads(blobs[E140 + 'manifest_tiny256.json'])
    assert len({r['run'] for r in labels}) == len(labels) == 1024
    assert len({r['cell'] for r in scores}) == len(scores) == 1024
    lookup = {r['cell']: r for r in scores}
    assert set(lookup) == {r['run'] for r in labels}
    rows = []
    for r in labels:
        s = lookup[r['run']]
        assert r['task'] == s['task'] and r['solver'] == s['agent']
        assert r['counted_all5'] in {'0', '1'}
        q = float(s['tc'])
        assert np.isfinite(q) and 0 <= q <= 1
        rows.append({'run': r['run'], 'task': r['task'], 'solver': r['solver'],
                     'score': q, 'y': int(r['counted_all5']),
                     'raw': int(r['lean_entails_raw']), 'four': int(r['lean_entails'])})
    tasks = {r['task'] for r in rows}
    solvers = {r['solver'] for r in rows}
    assert len(tasks) == 256 and len(solvers) == 4
    assert {(r['task'], r['solver']) for r in rows} == {(t, s) for t in tasks for s in solvers}
    return rows


def split_tasks(rows, config):
    tasks = sorted({r['task'] for r in rows}, key=lambda t: sha((config['split_salt'] + ':' + t).encode()))
    result, offset = {}, 0
    for split, count in config['task_counts'].items():
        result[split] = set(tasks[offset:offset + count])
        offset += count
    assert offset == len(tasks)
    return result


def fit_map(x, y, ridge):
    design = np.column_stack((np.ones(len(x)), x))

    def objective(beta):
        logits = design @ beta
        loss = np.mean(np.logaddexp(0, logits) - y * logits) + ridge * beta[1] ** 2 / 2
        grad = design.T @ (expit(logits) - y) / len(y) + np.array([0, ridge * beta[1]])
        return loss, grad

    fit = minimize(objective, [0.0, 0.0], jac=True, method='BFGS', options={'gtol': 1e-8})
    assert fit.success or np.max(np.abs(fit.jac)) < 1e-6, fit.message
    return fit.x


def corr(x, y):
    xc, yc = x - x.mean(axis=-1, keepdims=True), y - y.mean(axis=-1, keepdims=True)
    den = np.sqrt(np.sum(xc ** 2, axis=-1) * np.sum(yc ** 2, axis=-1))
    variable = (np.ptp(x, axis=-1) > 0) & (np.ptp(y, axis=-1) > 0)
    return np.divide(np.sum(xc * yc, axis=-1), den, out=np.full_like(den, np.nan), where=(den > 0) & variable)


def metrics(q, y):
    """Return metrics row-wise; arrays may have a leading bootstrap dimension."""
    ranks = rankdata(q, axis=-1)
    n1 = y.sum(axis=-1)
    n0 = y.shape[-1] - n1
    den = n1 * n0
    auc = np.divide((ranks * y).sum(axis=-1) - n1 * (n1 + 1) / 2, den,
                    out=np.full_like(den, np.nan, dtype=float), where=den > 0)
    return {'brier': np.mean((q - y) ** 2, axis=-1), 'mae': np.mean(np.abs(q-y), axis=-1),
            'bias': np.mean(q-y, axis=-1), 'mean_forecast': q.mean(axis=-1),
            'mean_outcome': y.mean(axis=-1), 'pearson': corr(q, y),
            'spearman': corr(ranks, rankdata(y, axis=-1)), 'auroc': auc}


def safe_float(x):
    return float(x) if np.isfinite(x) else None


def interval(x):
    finite = np.asarray(x)[np.isfinite(x)]
    return {'ci95': np.quantile(finite, [0.025, 0.975]).tolist() if len(finite) else None,
            'valid_resamples': len(finite)}


def evaluate(test, predictions, config):
    tasks = sorted({r['task'] for r in test})
    groups = [np.array([i for i, r in enumerate(test) if r['task'] == t]) for t in tasks]
    assert len({len(g) for g in groups}) == 1
    group_ids = np.stack(groups)
    rng = np.random.default_rng(config['bootstrap_seed'])
    sampled = rng.integers(0, len(tasks), (config['bootstrap_draws'], len(tasks)))
    indexes = group_ids[sampled].reshape(config['bootstrap_draws'], -1)
    y = np.array([r['y'] for r in test], dtype=float)
    output = {}
    for name, q in predictions.items():
        point = metrics(q, y)
        samples = metrics(q[indexes], y[indexes])
        point['kendall'] = kendalltau(q, y).statistic
        samples['kendall'] = np.array([kendalltau(q[ix], y[ix]).statistic for ix in indexes])
        output[name] = {k: {'value': safe_float(v), **interval(samples[k])} for k, v in point.items()}
    delta = (predictions['mapped']-y)**2 - (predictions['constant']-y)**2
    return {'artifacts': len(test), 'tasks': len(tasks), 'positives': int(y.sum()),
            'metrics': output, 'paired_brier_difference': {'value': float(delta.mean()),
                         **interval(delta[indexes].mean(axis=1))}}


def run_condition(rows, splits, config, excluded=None):
    train = [r for r in rows if r['task'] in splits['train'] and r['solver'] != excluded]
    validation = [r for r in rows if r['task'] in splits['validation'] and r['solver'] != excluded]
    test = [r for r in rows if r['task'] in splits['test'] and (excluded is None or r['solver'] == excluded)]
    x, y = np.array([r['score'] for r in train]), np.array([r['y'] for r in train])
    vx, vy = np.array([r['score'] for r in validation]), np.array([r['y'] for r in validation])
    tx = np.array([r['score'] for r in test])
    candidates = []
    for ridge in config['map_ridge_candidates']:
        beta = fit_map(x, y, ridge)
        loss = float(np.mean((expit(beta[0] + beta[1] * vx) - vy) ** 2))
        candidates.append({'ridge': ridge, 'coefficients': beta.tolist(), 'validation_brier': loss})
    best = min(candidates, key=lambda c: (c['validation_brier'], c['ridge']))
    beta = best['coefficients']
    predictions = {'mapped': expit(beta[0] + beta[1] * tx), 'constant': np.full(len(test), y.mean()), 'raw_scalar': tx}
    return {'excluded_solver': excluded, 'train_artifacts': len(train),
            'validation_artifacts': len(validation), 'training_prevalence': float(y.mean()),
            'candidates': candidates, 'selected_ridge': best['ridge'],
            'test': evaluate(test, predictions, config)}


def posthoc_diagnostics(rows, splits, condition):
    """Reviewer-requested descriptions; these never alter fitting or selection."""
    groups = {}
    for split, tasks in splits.items():
        for task in tasks:
            domain, _, rest = task.partition('__')
            if domain == 'security_set':
                match = re.search(r'__(\d+)_([a-z0-9]+?)(?:_safe)?$', rest)
                key = ('security', *match.groups()) if match else ('security', rest)
            else:
                rest = re.sub(r'_(safe|unsafe)$', '', rest.replace('heap_sort', 'heapsort'))
                tokens = re.split(r'_+', rest)
                key = (domain, '_'.join(tokens[:2]) if tokens[0] in ('humaneval', 'security') else tokens[0])
            groups.setdefault(key, []).append((task, split))
    cross = [g for g in groups.values() if len({s for _, s in g}) > 1]
    related = {t for g in cross for t, s in g if s == 'test' and any(s2 != 'test' for _, s2 in g)}
    test = [r for r in rows if r['task'] in splits['test']]
    best = next(c for c in condition['candidates'] if c['ridge'] == condition['selected_ridge'])
    b0, b1 = best['coefficients']
    bands = []
    for label, predicate in [('1.0', lambda x: x == 1), ('0.9', lambda x: x == .9),
                             ('0.8', lambda x: x == .8), ('0.7', lambda x: x == .7),
                             ('0.6', lambda x: x == .6), ('at most 0.5', lambda x: x <= .5)]:
        band = [r for r in test if predicate(r['score'])]
        if band:
            bands.append({'score_band': label, 'artifacts': len(band),
                          'tasks': len({r['task'] for r in band}), 'successes': sum(r['y'] for r in band),
                          'mean_forecast': float(np.mean([expit(b0+b1*r['score']) for r in band])),
                          'observed_rate': float(np.mean([r['y'] for r in band]))})
    return {'posthoc': True, 'family_key_is_name_heuristic_not_semantic_validation': True,
            'heuristic_families': len(groups), 'families_spanning_splits': len(cross),
            'test_tasks_with_fit_sibling': len(related), 'score_bands': bands}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-repo', type=Path, required=True)
    args = parser.parse_args()
    config = json.loads((ROOT / 'config.json').read_text())
    blobs, provenance = read_sources(args.source_repo, config['source_revision'])
    rows = load_rows(blobs)
    splits = split_tasks(rows, config)
    private = PROJECT / 'research_artifacts/prover_target'
    private.mkdir(parents=True, exist_ok=True)
    for path, content in blobs.items():
        dest = private / 'source' / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(content)
    dump(private / 'split_manifest.json', {k: sorted(v) for k, v in splits.items()})
    outputs = {'all_agents': run_condition(rows, splits, config)}
    for solver in sorted({r['solver'] for r in rows}):
        outputs['exclude_' + solver] = run_condition(rows, splits, config, solver)
    counts = {s: {key: sum(r[key] for r in rows if r['solver'] == s) for key in ('raw', 'four', 'y')}
              for s in sorted({r['solver'] for r in rows})}
    result = {'status': 'completed_retrospective_no_calls', 'fresh_validation': False,
              'config_sha256': sha((ROOT / 'config.json').read_bytes()),
              'script_sha256': sha(Path(__file__).read_bytes()),
              'source_revision': config['source_revision'], 'rows': len(rows),
              'tasks': len(splits['train'] | splits['validation'] | splits['test']),
              'missing_join_rows': 0, 'acceptance_counts': counts,
              'conditions': outputs, 'bootstrap_draws': config['bootstrap_draws'],
              'bootstrap_seed': config['bootstrap_seed'], 'p_value': None,
              'p_value_note': 'Descriptive retrospective analysis, no confirmatory test.',
              'repeat_search_variability': 'unavailable: one saved outcome per artifact',
              'posthoc_diagnostics': posthoc_diagnostics(rows, splits, outputs['all_agents']),
              'versions': {'python': platform.python_version(), 'numpy': np.__version__, 'scipy': scipy.__version__},
              'new_measured_model_calls': 0, 'incremental_measured_inference_usd': 0}
    dump(ROOT / 'results/retrospective.json', result)
    dump(ROOT / 'sources/provenance.json', {'source_access': 'restricted source repository; aggregate export only',
         'source_revision': config['source_revision'], 'files': provenance,
         'split_manifest_sha256': sha((private / 'split_manifest.json').read_bytes()),
         'config_sha256': result['config_sha256']})
    print(json.dumps({'rows':len(rows), 'conditions':list(outputs),
                      'primary_difference': outputs['all_agents']['test']['paired_brier_difference']}))


if __name__ == '__main__':
    main()
