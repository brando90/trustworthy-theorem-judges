#!/usr/bin/env python3
"""Compile every prespecified label certificate; keep all failures explicit."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import time
import tempfile
from build_controls import ROOT, create_cases, dump, sha
from certificate_checker import CertificateChecker


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--verify-existing', action='store_true', help='Recompile saved certificates without changing any tracked evidence')
    args = parser.parse_args()
    started = time.time()
    baseline_path = ROOT / 'results/certificate_validation.json'
    baseline = json.loads(baseline_path.read_text()) if args.verify_existing else None
    if not args.verify_existing and (ROOT / 'inference_freeze.json').exists():
        raise RuntimeError('Inference is frozen; use --verify-existing')
    output = args.output or (Path(tempfile.mkdtemp(prefix='ttj07_recheck_')) / 'certificate_validation.json' if args.verify_existing else baseline_path)
    if args.verify_existing and output.resolve().is_relative_to(ROOT):
        raise RuntimeError('Replay output must be outside the frozen experiment')
    manifest = json.loads((ROOT / 'construction_manifest.json').read_text())
    inputs = [json.loads(x) for x in (ROOT / 'inputs.jsonl').read_text().splitlines()]
    expected, expected_inputs = create_cases()
    assert manifest['rows'] == expected and inputs == expected_inputs, 'Construction differs from source'
    checker = CertificateChecker(args.lean)
    if baseline:
        assert checker.pins == baseline['pins'], 'Runtime/checker pins differ from saved validation'
        assert sha((ROOT / 'inputs.jsonl').read_bytes()) == baseline['input_sha256']
        assert sha((ROOT / 'construction_manifest.json').read_bytes()) == baseline['construction_manifest_sha256']
    prior = {r['id']: r for r in baseline['rows']} if baseline else {}
    rows, labels = [], []
    for case, item in zip(expected, inputs, strict=True):
        if time.time() - started > 1800:
            raise RuntimeError('CPU analysis budget exceeded')
        if case['predicted_status'] == 'unsupported':
            assert item['statement'].splitlines()[1] == 'axiom h0 : False'
            result = {'accepted': True, 'status': 'unsupported_statement_axiom',
                      'semantic_label': None, 'certificate': None,
                      'reason': 'Statement declares an additional axiom; outside the admitted axiom-free source grammar.'}
        else:
            result = checker.check(item['statement'], case['proofs'],
                                   ROOT / 'certificates' / (case['id'] + '.lean'),
                                   nonce=prior[case['id']]['audit_nonce'] if baseline else None,
                                   write=not args.verify_existing)
        rows.append({'id': case['id'], **result})
        status = case['predicted_status'] if result['accepted'] else 'unresolved'
        labels.append({k: case[k] for k in ('id', 'family', 'split', 'control_type', 'statement_sha256')} |
                      {'status': status, 'label': case['predicted_label'] if result['accepted'] else None,
                       'certificate': {'path': None if status == 'unsupported' else f"certificates/{case['id']}.lean",
                                       'source_sha256': result.get('source_sha256'),
                                       'targets': result.get('targets', []), 'accepted': result['accepted']}})
        print(case['id'], case['family'], case['control_type'], result['status'], flush=True)
        if not result['accepted']:
            print(result['compile']['output'], flush=True)
    result = {'schema_version': 1, 'all_construction_predictions_verified': all(r['accepted'] for r in rows),
              'pins': checker.pins, 'input_sha256': sha((ROOT / 'inputs.jsonl').read_bytes()),
              'construction_manifest_sha256': sha((ROOT / 'construction_manifest.json').read_bytes()),
              'generator_sha256': sha((ROOT / 'scripts/build_controls.py').read_bytes()),
              'verifier_sha256': sha(Path(__file__).read_bytes()),
              'total_controls': len(rows), 'status_counts': dict(Counter(x['status'] for x in labels)),
              'label_counts': dict(Counter(str(x['label']) for x in labels)),
              'elapsed_seconds': time.time() - started, 'rows': rows}
    output.parent.mkdir(parents=True, exist_ok=True)
    dump(output, result)
    if args.verify_existing:
        assert labels == json.loads((ROOT / 'labels.json').read_text()), 'Replayed labels differ'
    else:
        dump(ROOT / 'labels.json', labels)
    print(f'Validation receipt: {output}')
    return 0 if result['all_construction_predictions_verified'] else 1


if __name__ == '__main__':
    sys.exit(main())
