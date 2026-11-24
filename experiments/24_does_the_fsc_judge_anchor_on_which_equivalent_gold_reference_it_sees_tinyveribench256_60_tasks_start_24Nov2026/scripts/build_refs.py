"""Deterministic materials of experiment 24: G (gold, proofs replaced by sorry), N (natural agent, same treatment), Gother (G of the next task, cyclic).

Use: from the experiment folder: python3 scripts/build_refs.py. Needs python3 only. Writes materials/<task>/{G.lean,N.lean,Gother.lean} and materials/refs.json (sha256 of every file). No judge output is read.
Example: python3 scripts/build_refs.py
"""
import json, hashlib, pathlib, sys, os
sys.path.insert(0, os.path.dirname(__file__))
from lean_utils import replace_proofs, statements
HERE = pathlib.Path(__file__).resolve().parents[1]
tasks = json.load(open(HERE / 'inputs/tasks.json'))['tasks']
refs = {}
for i, t in enumerate(tasks):
    d = HERE / 'materials' / t; d.mkdir(parents=True, exist_ok=True)
    g = (HERE / 'inputs' / t / 'gold.lean').read_text(); n = (HERE / 'inputs' / t / 'historical_agent.lean').read_text()
    gs, ns = replace_proofs(g), replace_proofs(n)
    assert statements(gs) == statements(g), t  # statements untouched by the proof stripping
    gother = replace_proofs((HERE / 'inputs' / tasks[(i + 1) % len(tasks)] / 'gold.lean').read_text())
    for name, txt in (('G', gs), ('N', ns), ('Gother', gother)):
        (d / f'{name}.lean').write_text(txt); refs[f'{t}/{name}'] = hashlib.sha256(txt.encode()).hexdigest()
json.dump(refs, open(HERE / 'materials/refs.json', 'w'), indent=0)
print(len(tasks), 'tasks built')
