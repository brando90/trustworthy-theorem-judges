#!/usr/bin/env python3
"""TLDR: Snapshot pinned restricted prover sources and selected source contexts; export hashes only."""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT.parents[1]
PRIVATE = PROJECT / 'research_artifacts/fresh_prover_target'
VB = Path.home() / 'veribench'
INF = Path.home() / 'veribench-inf'
VB_REV = 'ec1f9b2a4455549ba98a4fdf94c9d30bf3a0522d'
INF_REV = '36a4d8b54aca7133e381601f285ffa4b7f82b28c'
E169 = 'experiments/169_natural_output_prover_fsc_validation_11-06-2026/'
E13 = 'experiments/13_tiny256_pi_prover_detection_false_alarm_11-04-2026/'
SELECTION = [('W1_024', 'string_length'), ('W1_101', 'prefix_filter'),
             ('W4_021', 'uri_permission'), ('W3_015', 'same_origin')]

def digest(data):
    return hashlib.sha256(data).hexdigest()

def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        assert path.read_bytes() == data, f'Immutable snapshot differs: {path}'
    else:
        path.write_bytes(data)

def dump(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + '\n')

def blob(repo, revision, name):
    return subprocess.check_output(['git', '-C', str(repo), 'show', revision + ':' + name])

def main():
    provenance = []
    def snapshot(repo, revision, source, destination):
        data = blob(repo, revision, source)
        save(PRIVATE / destination, data)
        provenance.append({'repository': repo.name, 'revision': revision, 'source': source,
                           'destination': destination, 'sha256': digest(data), 'bytes': len(data)})
        return data
    paths = {
        'scripts/vb169_service/trusted_checker.py': 'dependencies/trusted_checker.py',
        'scripts/lean/KernelReplayStrictSupport.lean': 'dependencies/KernelReplayStrictSupport.lean',
        'scripts/natural_contexts/export_contexts.py': 'dependencies/export_contexts.py',
        'scripts/natural_contexts/lean/ExtractSupport.lean': 'dependencies/ExtractSupport.lean',
        'results/natural_contexts/full100_ledger.json': 'source/full100_ledger.json',
    }
    for name, dest in paths.items(): snapshot(VB, VB_REV, E169 + name, dest)
    snapshot(INF, INF_REV, E13 + 'scripts/ProofOnly.lean', 'dependencies/ProofOnly.lean')
    ledger = json.loads((PRIVATE/'source/full100_ledger.json').read_text())['rows']
    cases = []
    for number, (module, family) in enumerate(SELECTION):
        r = next(row for row in ledger if row['module'] == module)
        assert r['status'] == 'emitted' and not r['witness']['axioms_outside_allowlist']
        assert r['match_tier'] != 'declared_adapter'
        assert r['lean_vs_source_names_agree']['gold'] and r['lean_vs_source_names_agree']['agent']
        assert len(r['extraction']['slots']) == 2
        ident = f'T{number+1:02}'
        stem = f'cases/{ident}/'
        context = snapshot(VB, VB_REV, E169 + f'results/natural_contexts/cases/{module}/Context.lean', stem+'OriginalContext.lean')
        assert digest(context) == r['context_sha256']
        source_revision = r['repo_commit']
        gold = snapshot(VB, source_revision, r['gold_path'], stem+'GoldSource.lean')
        agent = snapshot(VB, source_revision, r['solver_path'], stem+'OldAgentSource.lean')
        assert digest(gold) == r['gold_sha256'] and digest(agent) == r['solver_sha256']
        py_path = r['gold_path'].replace('lean_src/veribench/', 'py_src/').removesuffix('.lean')+'.py'
        python = snapshot(VB, source_revision, py_path, stem+'Input.py')
        source = context.decode()
        # The reference definition is extracted verbatim; a Lean equality check binds it later.
        start = source.index('def GoldSpec ')
        end = source.index('/-- Formal specification coverage:', start)
        gold_definition = source[start:end].strip()
        signature = gold_definition.split(' : Prop :=', 1)[0].removeprefix('def GoldSpec ')
        save(PRIVATE/(stem+'GoldDefinition.txt'), gold_definition.encode())
        row = {'id': ident, 'family': family, 'source_module': module, 'source_task': r['task'],
               'source_revision': source_revision, 'signature': signature,
               'slots': r['extraction']['slots'], 'gold_definition_sha256': digest(gold_definition.encode()),
               'context_sha256': digest(context), 'python_sha256': digest(python),
               'source_receipt': r}
        cases.append(row)
    dump(PRIVATE/'cases.json', cases)
    dump(ROOT/'sources/provenance.json', {'veribench_revision': VB_REV, 'infinity_revision': INF_REV,
         'source_population': {'attempted': 100, 'emitted': 14, 'unresolved': 86},
         'selected_source_tasks': len(cases), 'selection': 'purposive, two functions, no adapter, standard-axiom source witnesses; not a representative sample',
         'sources': provenance, 'private_case_manifest_sha256': digest((PRIVATE/'cases.json').read_bytes())})
    print('Saved pinned sources and four source-task contexts; no model calls.')

if __name__ == '__main__': main()
