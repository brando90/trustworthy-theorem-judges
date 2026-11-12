#!/usr/bin/env python3
"""TLDR: Check binary-loss identities, strict parsing, task separation and source-bound aggregate outputs."""
import hashlib
import json
from pathlib import Path
import numpy as np
from analyze import ROOT, PROJECT, metrics, split_tasks, fit_map


def parse_forecast(text):
    obj = json.loads(text)
    if set(obj) != {'probability_prover_accepts', 'reason'}:
        raise ValueError('unexpected schema')
    p = obj['probability_prover_accepts']
    if type(p) not in (int, float) or not np.isfinite(p) or not 0 <= p <= 1:
        raise ValueError('invalid probability')
    if not isinstance(obj['reason'], str):
        raise ValueError('invalid reason')
    return p


def main():
    y = np.array([0., 1., 0., 1.])
    assert metrics(y, y)['brier'] == 0
    assert metrics(1-y, y)['brier'] == 1
    assert metrics(np.full(4, .5), y)['brier'] == .25
    for p in (0, .2, .5, 1):
        for q in (0, .3, .7, 1):
            assert np.isclose(p*(q-1)**2+(1-p)*q*q, (q-p)**2+p*(1-p))
    assert parse_forecast('{"probability_prover_accepts":0.3,"reason":"bounded search"}') == .3
    for bad in ('true', '-0.1', '1.1', 'NaN', '"0.5"'):
        try:
            parse_forecast('{"probability_prover_accepts":'+bad+',"reason":"x"}')
        except ValueError:
            pass
        else:
            raise AssertionError('invalid response accepted')
    assert metrics(np.array([.1,.9,.1,.9]), y)['auroc'] == 1
    assert metrics(np.full(4, .5), y)['auroc'] == .5
    assert np.isnan(metrics(np.full(4, .5), y)['spearman'])
    for p in (.1, 157/192, 149/192):
        assert np.isnan(metrics(np.full(128, p), np.tile(y, 32))['pearson'])
    config = json.loads((ROOT/'config.json').read_text())
    rows = [{'task': str(i)} for i in range(256)]
    splits = split_tasks(rows, config)
    assert len(set.union(*splits.values())) == 256
    assert not splits['train'] & splits['validation']
    assert not splits['train'] & splits['test']
    assert not splits['validation'] & splits['test']
    beta = fit_map(np.array([0.,0.,1.,1.]), np.array([0.,1.,0.,1.]), .1)
    assert np.max(np.abs(beta)) < 1e-7
    result_path = ROOT/'results/retrospective.json'
    if result_path.exists():
        result = json.loads(result_path.read_text())
        assert result['config_sha256'] == hashlib.sha256((ROOT/'config.json').read_bytes()).hexdigest()
        assert result['script_sha256'] == hashlib.sha256((ROOT/'scripts/analyze.py').read_bytes()).hexdigest()
        assert result['rows'] == 1024 and result['missing_join_rows'] == 0
        for name, c in result['conditions'].items():
            assert c['test']['tasks'] == 128
            assert c['test']['artifacts'] == (512 if name == 'all_agents' else 128)
            assert c['train_artifacts'] == (256 if name == 'all_agents' else 192)
            assert c['validation_artifacts'] == c['train_artifacts']
            assert c['selected_ridge'] == min(c['candidates'], key=lambda d:(d['validation_brier'],d['ridge']))['ridge']
            assert c['test']['metrics']['constant']['pearson']['value'] is None
            assert c['test']['metrics']['constant']['pearson']['valid_resamples'] == 0
        assert sum(b['artifacts'] for b in result['posthoc_diagnostics']['score_bands']) == 512
    print('PASS: proper-loss identities, parsing, selection and task-disjoint denominators')


if __name__ == '__main__':
    main()
