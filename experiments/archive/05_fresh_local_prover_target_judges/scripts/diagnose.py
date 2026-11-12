#!/usr/bin/env python3
"""TLDR: Independently check post-outcome counterexamples without changing any frozen operational target."""
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
V2=ROOT/'conditions/nonthinking_v2'
spec=importlib.util.spec_from_file_location('v2_checker',V2/'scripts/checker.py')
checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
PRIVATE=checker.PRIVATE
PROOFS=json.loads((PRIVATE/'diagnostic_proposals.json').read_text())

def main():
    assert (PRIVATE/'done.json').exists(),'Do not contend with measured target search'
    artifacts={a['id']:a for a in json.loads((PRIVATE/'artifacts.json').read_text())}
    targets={a['artifact']:a for a in json.loads((PRIVATE/'targets.json').read_text())}
    rows=[]
    for ident,proof in PROOFS.items():
        a=artifacts[ident];assert targets[ident]['target']==0
        c=checker.Checker(PRIVATE/'diagnostics'/ident,a['context_source'])
        result=c.check(proof,'Natural.Counterexample')
        rows.append({'artifact':ident,'statement_sha256':a['statement_sha256'],'context_sha256':a['context_sha256'],
                     'independent_counterexample_checked':result['accepted'],'status':result['status'],
                     'proof_sha256':checker.sha(proof.encode()),'receipt_sha256':checker.sha(json.dumps(result,sort_keys=True).encode())})
        (PRIVATE/'diagnostics'/ident/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    outcome={'post_outcome_diagnostic':True,'target_outcomes_unchanged':True,'selection':'two unique well-formed statement cases; duplicate T01_G1 shares T01_G0 statement/context hashes',
             'model_calls':0,'rows':rows,'all_counterexamples_checked':all(r['independent_counterexample_checked'] for r in rows),
             'interpretation':'A checked counterexample separately demonstrates non-entailment for that exact statement; bounded search failure alone never does.'}
    (ROOT/'results/diagnostics.json').write_text(json.dumps(outcome,indent=2)+'\n')
    print(json.dumps(outcome))

if __name__=='__main__':main()
