#!/usr/bin/env python3
"""TLDR: Phase 0 zero-call transfer check of experiment 03's frozen probability map on Core-614 tasks outside Tiny-256; publishes aggregates only."""
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
from scipy.stats import rankdata

EXP = Path(__file__).resolve().parents[1]
PROJECT = EXP.parents[1]
E137 = 'experiments/137_public_vbv1_896_harsh_failure_reasons_and_smooth_components_10-30-2026/current_factors.jsonl'
E140 = 'experiments/140_entailment_check_vs_theorem_coverage_tiny256_10-31-2026/manifest_tiny256.json'
E145 = 'experiments/145_entailment_vacuity_axiom_check_tiny256_11-01-2026/results/per_run.csv'
E138 = 'experiments/138_tiny256_dt_10-31-2026/cells/'
SPLIT = PROJECT / 'private/prover_target/split_manifest.json'
PRIVATE = PROJECT / 'private/phase0_transfer'


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class Repo:
    def __init__(self, path):
        self.path, self.provenance = str(path), []

    def show(self, rev, name, record=True, missing_ok=False):
        out = subprocess.run(['git', '-C', self.path, 'show', f'{rev}:{name}'], capture_output=True)
        if out.returncode:
            if missing_ok:
                return None
            raise FileNotFoundError(f'{rev}:{name}')
        if record:
            self.provenance.append({'revision': rev, 'path': name, 'sha256': sha(out.stdout), 'bytes': len(out.stdout)})
        return out.stdout

    def ls(self, rev, prefix):
        out = subprocess.check_output(['git', '-C', self.path, 'ls-tree', '-r', '--name-only', rev, prefix])
        return out.decode().split()


def key(task):
    return task.replace('/', '__').lower()


def lean_features(text, regex, gold_theorems):
    """Deviation 1 (post-freeze, outcome-blind): a missing gold count gives ratio 0 and is counted."""
    missing_gold = int(not gold_theorems)
    if text is None:
        return {'thm_ratio': 0.0, 'log_lines': 0.0, 'missing_file': 1, 'missing_gold_count': missing_gold}
    body = text.decode('utf-8', errors='replace')
    n_thm = len(re.findall(regex, body, flags=re.MULTILINE))
    lines = sum(1 for line in body.splitlines() if line.strip())
    ratio = min(1.0, n_thm / gold_theorems) if gold_theorems else 0.0
    return {'thm_ratio': ratio, 'log_lines': float(np.log1p(lines)), 'missing_file': 0, 'missing_gold_count': missing_gold}


def gold_counts(rows, field):
    """Deviation 1: a row without its own gold count uses the task's largest count recorded for another solver."""
    best = {}
    for r in rows:
        if r[field].strip():
            best[key(r['task'])] = max(best.get(key(r['task']), 0), int(r[field]))
    filled = 0
    out = []
    for r in rows:
        if r[field].strip():
            out.append(int(r[field]))
        else:
            out.append(best.get(key(r['task']), 0))
            filled += key(r['task']) in best
    return out, filled


def fit_map(x, y, ridge):
    """Identical objective to experiment 03's fit_map (logistic log loss, slope ridge)."""
    design = np.column_stack((np.ones(len(x)), x))

    def objective(beta):
        logits = design @ beta
        loss = np.mean(np.logaddexp(0, logits) - y * logits) + ridge * beta[1] ** 2 / 2
        grad = design.T @ (expit(logits) - y) / len(y) + np.array([0, ridge * beta[1]])
        return loss, grad

    fit = minimize(objective, [0.0, 0.0], jac=True, method='BFGS', options={'gtol': 1e-8})
    assert fit.success or np.max(np.abs(fit.jac)) < 1e-6, fit.message
    return fit.x


def load_tiny(repo, cfg):
    rev = cfg['tiny256_source_revision']
    labels = list(csv.DictReader(io.StringIO(repo.show(rev, E145).decode())))
    scores = {r['cell']: r for r in json.loads(repo.show(rev, E140))}
    assert len(labels) == len(scores) == 1024 and {r['run'] for r in labels} == set(scores)
    rows, sha_mismatch = [], 0
    golds, _ = gold_counts(labels, 'k_gold')
    for r, gold in zip(labels, golds):
        cell = f"{E138}{r['solver']}/{r['task']}/"
        text = repo.show(rev, cell + 'solver.lean', record=False, missing_ok=True)
        receipt = repo.show(rev, cell + 'receipt.json', record=False, missing_ok=True)
        if text is not None and receipt is not None:
            sha_mismatch += json.loads(receipt).get('solver_lean_sha256') != sha(text)
        feats = lean_features(text, cfg['theorem_regex'], gold)
        rows.append({'task': r['task'], 'solver': r['solver'], 'fsc': float(scores[r['run']]['tc']),
                     'y': int(r['counted_all5']), **feats})
    return rows, sha_mismatch


def load_core(repo, cfg):
    rev = cfg['veribench_main_revision']
    ratings = {}
    for line in repo.show(rev, E137).decode().splitlines():
        d = json.loads(line)
        k = (key(d['task']), d['system'])
        assert k not in ratings
        ratings[k] = d['FSC_cov']
    rows, sha_checked, sha_mismatch = [], 0, 0
    raw = {exp: list(csv.DictReader(io.StringIO(repo.show(rev, f'experiments/{exp}/lean_entailment/E_LEAN_CHECKED.csv').decode())))
           for exp in cfg['core614_batches']}
    golds, filled = gold_counts([r for exp in raw for r in raw[exp]], 'gold_theorems')
    gold_iter = iter(golds)
    for exp, (solver, batch) in cfg['core614_batches'].items():
        base = f'experiments/{exp}/'
        manifests = {}
        for name in repo.ls(rev, base + 'inputs/'):
            if 'solver_sha_manifest' in name:
                manifests.update(json.loads(repo.show(rev, name)).get(solver, {}))
        converted = set(cfg['retry_converted_runs'].get(exp, []))
        seen = set()
        for r in raw[exp]:
            gold = next(gold_iter)
            final = int(r['E_lean'])
            assert final in (0, 1)
            if r['mod'] in converted:
                assert final == 1, (exp, r['mod'])
                seen.add(r['mod'])
            text = repo.show(rev, f"{base}runs/{solver}/{r['task']}/solver.lean", record=False, missing_ok=True)
            if text is not None and r['task'] in manifests:
                sha_checked += 1
                sha_mismatch += manifests[r['task']] != sha(text)
            fsc = ratings[(key(r['task']), cfg['rating_system_names'][solver])]
            assert fsc is not None and 0 <= fsc <= 1
            feats = lean_features(text, cfg['theorem_regex'], gold)
            rows.append({'task': r['task'], 'solver': solver, 'batch': batch, 'fsc': float(fsc),
                         'y': 0 if r['mod'] in converted else final, 'y_final': final, **feats})
        assert seen == converted, (exp, converted - seen)
    pairs = [(key(r['task']), r['solver']) for r in rows]
    assert len(pairs) == len(set(pairs)), 'duplicate (task, solver) rows'
    return rows, sha_checked, sha_mismatch, filled


def corr(x, y):
    xc, yc = x - x.mean(), y - y.mean()
    den = np.sqrt(np.sum(xc ** 2) * np.sum(yc ** 2))
    return float(np.sum(xc * yc) / den) if den > 0 and np.ptp(x) > 0 and np.ptp(y) > 0 else np.nan


def metrics(q, y):
    n1 = y.sum()
    n0 = len(y) - n1
    rq = rankdata(q)
    if n1 > 0 and n0 > 0:
        auc = ((rq * y).sum() - n1 * (n1 + 1) / 2) / (n1 * n0)
        _, counts = np.unique(q, return_counts=True)
        n = len(y)
        pairs = n * (n - 1) / 2
        tq = np.sum(counts * (counts - 1) / 2)
        ty = n1 * (n1 - 1) / 2 + n0 * (n0 - 1) / 2
        den = np.sqrt((pairs - tq) * (pairs - ty))
        kendall = n1 * n0 * (2 * auc - 1) / den if den > 0 else np.nan
    else:
        auc = kendall = np.nan
    return {'brier': np.mean((q - y) ** 2), 'mae': np.mean(np.abs(q - y)), 'bias': np.mean(q - y),
            'mean_forecast': q.mean(), 'mean_outcome': y.mean(), 'pearson': corr(q, y),
            'spearman': corr(rq, rankdata(y)), 'kendall': kendall, 'auroc': auc}


def summarize(values):
    finite = np.asarray(values, dtype=float)
    finite = finite[np.isfinite(finite)]
    return {'ci95': np.quantile(finite, [0.025, 0.975]).tolist() if len(finite) else None,
            'valid_resamples': int(len(finite))}


def num(x):
    return float(x) if np.isfinite(x) else None


def evaluate(rows, preds, ykey, cfg, paired):
    tasks = sorted({r['task'] for r in rows})
    index = {t: i for i, t in enumerate(tasks)}
    groups = [[] for _ in tasks]
    for i, r in enumerate(rows):
        groups[index[r['task']]].append(i)
    groups = [np.array(g) for g in groups]
    y = np.array([r[ykey] for r in rows], dtype=float)
    rng = np.random.default_rng(cfg['bootstrap_seed'])
    draws = rng.integers(0, len(tasks), (cfg['bootstrap_draws'], len(tasks)))
    samples = {name: {m: [] for m in metrics(q, y)} for name, q in preds.items()}
    diffs = {f'{a}_minus_{b}': [] for a, b in paired}
    sq = {name: (q - y) ** 2 for name, q in preds.items()}
    for d in draws:
        ix = np.concatenate([groups[j] for j in d])
        for name, q in preds.items():
            for m, v in metrics(q[ix], y[ix]).items():
                samples[name][m].append(v)
        for a, b in paired:
            diffs[f'{a}_minus_{b}'].append(np.mean(sq[a][ix] - sq[b][ix]))
    out = {'artifacts': len(rows), 'tasks': len(tasks), 'positives': int(y.sum()), 'metrics': {}, 'paired_brier_difference': {}}
    for name, q in preds.items():
        point = metrics(q, y)
        out['metrics'][name] = {m: {'value': num(v), **summarize(samples[name][m])} for m, v in point.items()}
    for a, b in paired:
        k = f'{a}_minus_{b}'
        out['paired_brier_difference'][k] = {'value': float(np.mean(sq[a] - sq[b])), **summarize(diffs[k])}
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-repo', required=True, help='authorized VeriBench checkout with both revisions')
    args = parser.parse_args()
    cfg_path = EXP / 'config_phase0.json'
    cfg = json.loads(cfg_path.read_text())
    repo = Repo(args.source_repo)
    e03 = json.loads((PROJECT / cfg['experiment03_results']).read_text())
    e03cfg = json.loads((PROJECT / cfg['experiment03_config']).read_text())
    cond = e03['conditions'][cfg['frozen_map_condition']]
    chosen = next(c for c in cond['candidates'] if c['ridge'] == cond['selected_ridge'])
    assert np.allclose(chosen['coefficients'], cfg['frozen_map_coefficients'], atol=1e-12)
    assert abs(cond['training_prevalence'] - cfg['frozen_constant']) < 5e-7

    tiny, tiny_sha_mismatch = load_tiny(repo, cfg)
    core, core_sha_checked, core_sha_mismatch, core_gold_filled = load_core(repo, cfg)
    splits = {k: set(v) for k, v in json.loads(SPLIT.read_text()).items()}
    order = sorted({r['task'] for r in tiny}, key=lambda t: sha((e03cfg['split_salt'] + ':' + t).encode()))
    counts = e03cfg['task_counts']
    recomputed = {'train': set(order[:counts['train']]),
                  'validation': set(order[counts['train']:counts['train'] + counts['validation']]),
                  'test': set(order[counts['train'] + counts['validation']:])}
    assert recomputed == splits, 'split manifest does not reproduce experiment 03 split'
    tiny_tasks = {key(r['task']) for r in tiny}
    overlap = {key(r['task']) for r in core} & tiny_tasks
    assert not overlap, f'{len(overlap)} Core-614 tasks also in Tiny-256'

    train = [r for r in tiny if r['task'] in splits['train']]
    val = [r for r in tiny if r['task'] in splits['validation']]
    ytr = np.array([r['y'] for r in train], dtype=float)
    yva = np.array([r['y'] for r in val], dtype=float)
    fits = {}
    for feat in ('fsc', 'thm_ratio', 'log_lines'):
        cands = []
        for ridge in cfg['baseline_ridge_candidates']:
            beta = fit_map(np.array([r[feat] for r in train]), ytr, ridge)
            loss = float(np.mean((expit(beta[0] + beta[1] * np.array([r[feat] for r in val])) - yva) ** 2))
            cands.append({'ridge': ridge, 'coefficients': beta.tolist(), 'validation_brier': loss})
        best = min(cands, key=lambda c: (c['validation_brier'], c['ridge']))
        fits[feat] = {'candidates': cands, 'selected_ridge': best['ridge'], 'coefficients': best['coefficients']}
    refit_gap = float(np.max(np.abs(np.array(fits['fsc']['coefficients']) - np.array(cfg['frozen_map_coefficients']))))
    assert refit_gap < 1e-4, f'refit does not reproduce frozen map: {refit_gap}'
    solver_prev = {s: float(np.mean([r['y'] for r in train if r['solver'] == s])) for s in sorted({r['solver'] for r in train})}

    def predictions(rows):
        x = {f: np.array([r[f] for r in rows]) for f in ('fsc', 'thm_ratio', 'log_lines')}
        b0, b1 = cfg['frozen_map_coefficients']
        return {'mapped': expit(b0 + b1 * x['fsc']),
                'constant': np.full(len(rows), cfg['frozen_constant']),
                'raw_scalar': x['fsc'],
                'thm_ratio_map': expit(fits['thm_ratio']['coefficients'][0] + fits['thm_ratio']['coefficients'][1] * x['thm_ratio']),
                'length_map': expit(fits['log_lines']['coefficients'][0] + fits['log_lines']['coefficients'][1] * x['log_lines']),
                'solver_prevalence': np.array([solver_prev[r['solver']] for r in rows])}

    paired = [('mapped', 'constant'), ('mapped', 'thm_ratio_map'), ('mapped', 'length_map'),
              ('mapped', 'solver_prevalence'), ('thm_ratio_map', 'constant'), ('length_map', 'constant'),
              ('solver_prevalence', 'constant')]
    y = np.array([r['y'] for r in core], dtype=float)
    controls = {'oracle': float(np.mean((y - y) ** 2)), 'half': float(np.mean((0.5 - y) ** 2)),
                'complement': float(np.mean(((1 - y) - y) ** 2))}
    assert controls == {'oracle': 0.0, 'half': 0.25, 'complement': 1.0}
    subsets = {'pooled': core}
    for b in ('first_batch', 'security'):
        subsets[b] = [r for r in core if r['batch'] == b]
    for s in sorted({r['solver'] for r in core}):
        subsets['solver_' + s] = [r for r in core if r['solver'] == s]
    results = {name: evaluate(rows, predictions(rows), 'y', cfg, paired) for name, rows in subsets.items()}
    results['pooled_final_outcomes_sensitivity'] = evaluate(core, predictions(core), 'y_final', cfg, paired[:1])

    bands = []
    q = predictions(core)['mapped']
    for label, pred in [('1.0', lambda v: v == 1), ('0.9', lambda v: abs(v - .9) < 1e-9), ('0.8', lambda v: abs(v - .8) < 1e-9),
                        ('0.7', lambda v: abs(v - .7) < 1e-9), ('0.6', lambda v: abs(v - .6) < 1e-9), ('at most 0.5', lambda v: v <= .5 + 1e-9)]:
        idx = [i for i, r in enumerate(core) if pred(r['fsc'])]
        if idx:
            bands.append({'rating': label, 'artifacts': len(idx), 'tasks': len({core[i]['task'] for i in idx}),
                          'successes': int(sum(core[i]['y'] for i in idx)), 'mean_forecast': float(np.mean(q[idx])),
                          'observed_rate': float(np.mean([core[i]['y'] for i in idx]))})

    out = {
        'status': 'phase0_transfer_complete', 'fresh_validation': False,
        'config_sha256': sha(cfg_path.read_bytes()), 'script_sha256': sha(Path(__file__).read_bytes()),
        'experiment03_results_sha256': sha((PROJECT / cfg['experiment03_results']).read_bytes()),
        'split_manifest_sha256': sha(SPLIT.read_bytes()),
        'tiny256_fit_rows': {'train': len(train), 'validation': len(val), 'training_prevalence': float(ytr.mean())},
        'tiny256_candidate_files_missing': int(sum(r['missing_file'] for r in tiny)),
        'tiny256_candidate_sha_mismatch_vs_receipt': int(tiny_sha_mismatch),
        'core614_rows': len(core), 'core614_tasks': len({r['task'] for r in core}),
        'core614_candidate_files_missing': int(sum(r['missing_file'] for r in core)),
        'core614_candidate_sha_checked': core_sha_checked, 'core614_candidate_sha_mismatch': core_sha_mismatch,
        'core614_tiny256_task_overlap': 0,
        'deviation1_core614_gold_count_filled_from_task': core_gold_filled,
        'deviation1_core614_rows_without_own_gold_count': int(sum(r['missing_gold_count'] for r in core)),
        'deviation1_tiny256_rows_without_own_gold_count': int(sum(r['missing_gold_count'] for r in tiny)),
        'primary_positives_first_pass': int(y.sum()), 'final_positives': int(sum(r['y_final'] for r in core)),
        'refit_gap_vs_frozen_map': refit_gap, 'baseline_fits': fits, 'solver_prevalence': solver_prev,
        'controls': controls, 'conditions': results, 'rating_bands_pooled': bands,
        'bootstrap_draws': cfg['bootstrap_draws'], 'bootstrap_seed': cfg['bootstrap_seed'],
        'p_value': 'n/a', 'new_measured_model_calls': 0, 'incremental_measured_inference_usd': 0,
        'versions': {'python': platform.python_version(), 'numpy': np.__version__, 'scipy': scipy.__version__},
    }
    (EXP / 'results').mkdir(exist_ok=True)
    (EXP / 'results/phase0_transfer.json').write_text(json.dumps(out, indent=2, allow_nan=False) + '\n')
    (EXP / 'results/phase0_sources.json').write_text(json.dumps({'source_access': 'restricted VeriBench repository; aggregate export only',
                                                                  'files': repo.provenance}, indent=2) + '\n')
    PRIVATE.mkdir(parents=True, exist_ok=True)
    (PRIVATE / 'core614_rows.json').write_text(json.dumps(core, indent=1) + '\n')
    print(json.dumps({k: out[k] for k in ('core614_rows', 'core614_tasks', 'primary_positives_first_pass',
                                         'core614_candidate_sha_mismatch', 'tiny256_candidate_sha_mismatch_vs_receipt',
                                         'refit_gap_vs_frozen_map')}, indent=1))


if __name__ == '__main__':
    main()
