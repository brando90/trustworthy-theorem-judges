#!/usr/bin/env python3
"""TLDR: Freeze actual source, code, prompt, model, cell and runtime dependency identities before inference."""
import datetime
import hashlib
import json
import subprocess
from pathlib import Path
from checker import ROOT, PRIVATE, LEAN_PROJECT, sha

def main():
    assert not (PRIVATE/'run_state.json').exists(), 'Never replace a freeze after any call reservation'
    config=json.loads((ROOT/'config.json').read_text())
    manifest=json.loads((LEAN_PROJECT/'lake-manifest.json').read_text())
    mathlib=next(p for p in manifest['packages'] if p['name']=='mathlib')
    package=LEAN_PROJECT/'.lake/packages/mathlib'
    revision=subprocess.check_output(['git','-C',str(package),'rev-parse','HEAD'],text=True).strip()
    assert revision==mathlib['rev']
    assert not subprocess.check_output(['git','-C',str(package),'diff','--name-only'],text=True).strip()
    lean=Path(subprocess.check_output(['elan','which','lean'],cwd=LEAN_PROJECT,text=True).strip())
    dependency_files=[LEAN_PROJECT/'lake-manifest.json',LEAN_PROJECT/'lean-toolchain',lean,
                      package/'lake-manifest.json', package/'.lake/build/lib/lean/Mathlib.olean',
                      lean.parent.parent/'lib/lean/Lean.olean',lean.parent.parent/'lib/lean/Init.olean']
    runtime={str(p):sha(p.read_bytes()) for p in dependency_files}
    cells={}
    for j,s in config['judge'].items():
        for kind in ['reproduce','semantic']:
            for i in range(2):cells[f'preflight_{j}_{kind}{i}']={'num_predict':s['num_predict'],'role':'preflight'}
    for task in config['task_ids']:
        for g,s in config['generator'].items():
            a=task+'_'+g
            cells['generate_'+a]={'num_predict':s['num_predict'],'role':'generation'}
            for j,sj in config['judge'].items():
                for k in range(3 if a in config['repeat_artifacts'] else 1):
                    cells[f'forecast_{a}_{j}_{k}']={'num_predict':sj['num_predict'],'role':'forecast'}
            for k in range(2):cells[f'prove_{a}_{k}']={'num_predict':config['prover']['num_predict'],'role':'proof_search'}
    assert len(cells)==config['maximum_calls']==56
    assert sum(x['num_predict'] for x in cells.values())==config['maximum_generated_tokens_reserved']==81920
    files=[ROOT/'config.json',ROOT/'PROTOCOL.md',ROOT/'results/target_checks.json',ROOT/'sources/provenance.json']
    files += sorted((ROOT/'scripts').glob('*.py'))+sorted((ROOT/'prompts').glob('*.md'))
    value={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'condition':config['condition'],'files':{str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in files},
           'runtime_dependencies':runtime,'mathlib_revision':revision,
           'lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),
           'ollama_version':config['ollama_version'],'model_digest':config['model_digest'],
           'private_case_manifest_sha256':sha((PRIVATE/'cases.json').read_bytes()),'planned_calls':cells,
           'code_commit_before_freeze':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()}
    (ROOT/'sources/freeze.json').write_text(json.dumps(value,indent=2)+'\n')
    print(json.dumps({'planned_calls':len(cells),'maximum_generated_tokens':sum(x['num_predict'] for x in cells.values()),'mathlib_revision':revision,'runtime_files':len(runtime)}))

if __name__=='__main__':main()
