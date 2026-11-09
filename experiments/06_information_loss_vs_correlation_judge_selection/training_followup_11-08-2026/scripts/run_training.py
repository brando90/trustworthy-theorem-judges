"""TLDR: Execute frozen mixture and softmax training on historical family-held-out folds."""
import argparse
import collections
import hashlib
import json
import platform
from pathlib import Path
import sys
import time
import warnings

import numpy as np
import scipy

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT.parent / 'scripts'))
from metrics import histogram, per_item, smooth, summarize
from run_cached import dump, partitions
from mixture_models import fit_mixture, predict_mixture
from check_mixtures import controls as mixture_controls
from weighted_softmax import fit, predict, controls as softmax_controls


def interval(values):
    values = np.asarray(values, dtype=float)
    valid = values[np.isfinite(values)]
    return {'lo': float(np.quantile(valid, .025)) if len(valid) else None,
            'hi': float(np.quantile(valid, .975)) if len(valid) else None,
            'valid_draws': len(valid), 'invalid_draws': len(values)-len(valid)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--data', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--private-out', required=True)
    ap.add_argument('--controls-only', action='store_true')
    args = ap.parse_args()
    cfg = json.loads((ROOT / 'protocol.json').read_text())
    controls = {'mixture': mixture_controls(), 'softmax': softmax_controls()}
    if args.controls_only:
        print(json.dumps(controls, indent=2)); return
    out, private = Path(args.out), Path(args.private_out)
    out.mkdir(parents=True, exist_ok=True); private.mkdir(parents=True, exist_ok=True)
    assert not (out / 'results.json').exists(), 'Preserve completed results.'
    data_path = Path(args.data)
    digest = hashlib.sha256(data_path.read_bytes()).hexdigest()
    assert digest == cfg['dataset_sha256']
    data = json.loads(data_path.read_text()); rows = data['rows']; n = len(rows)
    assert n == 75 and len({r['task'] for r in rows}) == 25
    assert set(collections.Counter(r['task'] for r in rows).values()) == {3}
    p = np.array([histogram(r['ratings']) for r in rows])
    q = np.stack([smooth(np.array([histogram(v) for v in data['outputs'][name]]),
                         cfg['epsilon']) for name in cfg['candidate_order']], axis=1)
    x = np.array([np.mean(data['outputs'][name], axis=1)/5
                  for name in cfg['candidate_order']]).T
    parts = partitions(rows, cfg['seeds'])
    mix_names = ['mixture_' + name for name in cfg['mixture_objectives']]
    soft_names = ['softmax_' + name for name in cfg['softmax_objectives']]
    methods = mix_names + soft_names + ['constant']
    outputs = {name: [] for name in methods}
    models, fit_models, mix_fits, soft_fits, choices = [], [], [], [], []
    start = time.monotonic()
    warnings.filterwarnings('ignore', message='An input array is constant')

    def progress(**state):
        state.update(elapsed_seconds=time.monotonic()-start)
        dump(out / 'progress.json', state); print(json.dumps(state), flush=True)

    def disjoint(train, test):
        assert not ({rows[i]['family'] for i in train} & {rows[i]['family'] for i in test})

    for si, (outer, inners) in enumerate(parts):
        forecasts = {name: np.full((n, 6), np.nan) for name in methods}
        for fold in range(5):
            tr = np.flatnonzero(outer != fold); te = np.flatnonzero(outer == fold)
            disjoint(tr, te)
            common = {'seed_index': si, 'fold': fold, 'train_indices': tr,
                      'test_indices': te}
            for loss, name in zip(cfg['mixture_objectives'], mix_names):
                weights, receipt = fit_mixture(q[tr], p[tr], loss)
                mix_fits.append({'seed_index': si, 'fold': fold, 'method': name, **receipt})
                dump(out / 'mixture_fit_receipts.json', mix_fits)
                assert receipt['success'], receipt
                forecasts[name][te] = predict_mixture(q[te], weights)
                models.append({**common, 'method': name, 'model': {'weights': weights}})
            mean_p = smooth(p[tr].mean(0), cfg['epsilon'])
            forecasts['constant'][te] = mean_p
            models.append({**common, 'method': 'constant', 'model': {'pmf': mean_p}})
            inner = inners[fold]
            for loss, name in zip(cfg['softmax_objectives'], soft_names):
                scores = []
                for strength in cfg['l2_strengths']:
                    held = np.full((len(tr), 6), np.nan)
                    for f in range(4):
                        train = tr[[inner[rows[i]['family']] != f for i in tr]]
                        valid_local = np.flatnonzero([inner[rows[i]['family']] == f for i in tr])
                        valid = tr[valid_local]; disjoint(train, valid)
                        model, rec = fit(x[train], p[train], loss, strength,
                                         cfg['seeds'][si]+100*fold+f, cfg['softmax_optimizer'])
                        fit_models.append({'public_fit_index': len(soft_fits),
                                           'train_indices': train, 'model': model})
                        soft_fits.append({'seed_index': si, 'fold': fold, 'inner_fold': f,
                                          'method': name, **rec})
                        assert rec['finite'], rec
                        held[valid_local] = smooth(predict(model, x[valid]), cfg['epsilon'])
                    assert np.isfinite(held).all()
                    scores.append(float(per_item(p[tr], held)['rps'].mean()))
                chosen = min(range(len(scores)), key=lambda j: (scores[j], j))
                strength = cfg['l2_strengths'][chosen]
                model, rec = fit(x[tr], p[tr], loss, strength,
                                 cfg['seeds'][si]+100*fold+99, cfg['softmax_optimizer'])
                fit_models.append({'public_fit_index': len(soft_fits),
                                   'train_indices': tr, 'model': model})
                soft_fits.append({'seed_index': si, 'fold': fold, 'inner_fold': None,
                                  'method': name, **rec})
                assert rec['finite'], rec
                forecasts[name][te] = smooth(predict(model, x[te]), cfg['epsilon'])
                models.append({**common, 'method': name, 'model': model})
                choices.append({'seed_index': si, 'fold': fold, 'method': name,
                                'strength': strength, 'inner_rps': scores})
            progress(phase='training', completed_outer_folds=si*5+fold+1,
                     mixture_fits=len(mix_fits), softmax_fits=len(soft_fits))
        for name in methods:
            assert np.isfinite(forecasts[name]).all() and (forecasts[name] > 0).all()
            assert np.allclose(forecasts[name].sum(1), 1, atol=1e-12, rtol=0)
            outputs[name].append(forecasts[name])
        dump(private / 'partial_forecasts.json', {'outputs': outputs, 'models': models,
             'softmax_fit_models': fit_models, 'completed_seeds': si+1})
    assert len(mix_fits) == cfg['expected_mixture_fits']
    assert len(soft_fits) == cfg['expected_softmax_fits']
    assert len(choices) == cfg['expected_softmax_choices']
    dump(private / 'forecasts.json', {'outputs': outputs, 'models': models,
         'softmax_fit_models': fit_models,
         'partitions': [{'outer': outer, 'inner': inner} for outer, inner in parts]})
    items = {name: [per_item(p, forecast) for forecast in values] for name, values in outputs.items()}

    def aggregate(index, item_values=items):
        result = {}
        for name, values in item_values.items():
            per_seed = [summarize(value, index) for value in values]
            result[name] = {metric: float(np.mean([v[metric] for v in per_seed]))
                            for metric in per_seed[0]}
        return result

    matrix = aggregate(np.arange(n)); metrics = list(matrix[methods[0]])
    contrasts = {'mixture_weighted_minus_pearson': ('mixture_weighted_pmf', 'mixture_pearson'),
                 **{'softmax_weighted_minus_'+loss: ('softmax_weighted_pmf', 'softmax_'+loss)
                    for loss in ['ce', 'brier', 'rps']}}
    conditional = {name: {metric: [] for metric in metrics} for name in methods}
    differences = {name: {metric: [] for metric in metrics} for name in contrasts}
    refit_differences = {metric: [] for metric in metrics}
    families = np.array([r['family'] for r in rows]); fam = sorted(set(families))
    assert len(fam) == 19
    rng = np.random.default_rng(cfg['bootstrap_seed']); ledger = []
    for b in range(cfg['bootstrap_draws']):
        draw = rng.choice(fam, size=len(fam), replace=True)
        ix = np.concatenate([np.flatnonzero(families == family) for family in draw])
        a = aggregate(ix)
        for name in methods:
            for metric in metrics: conditional[name][metric].append(a[name][metric])
        for name, (first, second) in contrasts.items():
            for metric in metrics: differences[name][metric].append(a[first][metric]-a[second][metric])
        valid = True; refit_values = {name: [] for name in mix_names}; certificates = []
        undefined = 0; failure = None
        for si, (outer, _) in enumerate(parts):
            fitted = {name: np.full((len(ix), 6), np.nan) for name in mix_names}
            for fold in range(5):
                train = ix[outer[ix] != fold]; test_local = np.flatnonzero(outer[ix] == fold)
                test = ix[test_local]
                if not len(test): continue
                if len(train) < 2:
                    valid = False; failure = 'empty_or_single_row_training'; break
                for loss, name in zip(cfg['mixture_objectives'], mix_names):
                    weights, rec = fit_mixture(q[train], p[train], loss)
                    certificates.append(bool(rec['success']))
                    undefined += int(rec['undefined_correlation'])
                    if not rec['success']:
                        valid = False; failure = 'optimality_certificate_failed'; break
                    fitted[name][test_local] = predict_mixture(q[test], weights)
                if not valid: break
            if not valid: break
            for name in mix_names:
                assert np.isfinite(fitted[name]).all()
                refit_values[name].append(summarize(per_item(p[ix], fitted[name]), np.arange(len(ix))))
        for metric in metrics:
            delta = (np.mean([v[metric] for v in refit_values[mix_names[0]]])
                     - np.mean([v[metric] for v in refit_values[mix_names[1]]])) if valid else np.nan
            refit_differences[metric].append(float(delta))
        ledger.append({'draw': b, 'unique_families': len(set(draw)), 'valid': valid,
                       'reason': failure, 'fits': len(certificates),
                       'certificate_failures': sum(not value for value in certificates),
                       'undefined_training_correlations': undefined})
        if (b+1) % 25 == 0:
            dump(private / 'bootstrap_partial.json', {'completed_draws': b+1, 'ledger': ledger})
            progress(phase='bootstrap_refitting', completed=b+1, total=cfg['bootstrap_draws'])
    dump(private / 'bootstrap.json', {'conditional': conditional, 'differences': differences,
         'refit_differences': refit_differences, 'ledger': ledger})
    result = {'methods': methods, 'matrix': matrix,
              'conditional_intervals': {name: {metric: interval(values) for metric, values in d.items()}
                                        for name, d in conditional.items()},
              'conditional_differences': {name: {metric: {'estimate': matrix[contrasts[name][0]][metric]
                                        - matrix[contrasts[name][1]][metric], **interval(values)}
                                        for metric, values in d.items()} for name, d in differences.items()},
              'mixture_refit_differences': {metric: {'estimate': matrix[mix_names[0]][metric]
                                        - matrix[mix_names[1]][metric], **interval(values)}
                                        for metric, values in refit_differences.items()},
              'mixture_fits': mix_fits, 'softmax_fits': soft_fits, 'softmax_choices': choices,
              'counts': {'artifacts': n, 'tasks': 25, 'families': 19,
                         'expert_ratings': sum(len(r['ratings']) for r in rows),
                         'mixture_fits': len(mix_fits), 'softmax_fits': len(soft_fits),
                         'softmax_choices': len(choices), 'final_models': len(models),
                         'artifact_forecasts': len(methods)*len(parts)*n,
                         'softmax_nonconverged': sum(not r['success'] for r in soft_fits),
                         'mixture_refit_bootstrap_draws': len(ledger),
                         'mixture_refit_invalid_draws': sum(not r['valid'] for r in ledger),
                         'mixture_bootstrap_fits': sum(r['fits'] for r in ledger)},
              'per_seed': {name: [summarize(v, np.arange(n)) for v in values] for name, values in items.items()},
              'resplit_standard_deviations': {name: {metric: float(np.std([summarize(v, np.arange(n))[metric]
                                              for v in values], ddof=1)) for metric in metrics}
                                              for name, values in items.items()},
              'controls': controls, 'elapsed_seconds': time.monotonic()-start,
              'protocol_sha256': hashlib.sha256((ROOT/'protocol.json').read_bytes()).hexdigest(),
              'dataset_sha256': digest, 'python': platform.python_version(),
              'numpy': np.__version__, 'scipy': scipy.__version__,
              'new_inference_calls': 0, 'provider_cost_usd': 0}
    dump(out / 'results.json', result)
    progress(phase='complete', status='COMPLETE', counts=result['counts'])


if __name__ == '__main__':
    main()
