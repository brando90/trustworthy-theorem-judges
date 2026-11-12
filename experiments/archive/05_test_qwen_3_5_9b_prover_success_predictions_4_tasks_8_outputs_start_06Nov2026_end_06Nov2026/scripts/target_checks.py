#!/usr/bin/env python3
"""TLDR: Re-extract pinned source contexts and test strict fixed-goal acceptance before model calls."""
import concurrent.futures
import importlib.util
import json
from pathlib import Path
from checker import Checker, PRIVATE, ROOT, context, sha

def load_exporter():
    file=PRIVATE/'dependencies/export_contexts.py'
    spec=importlib.util.spec_from_file_location('source_exporter',file)
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    module.REPO=Path.home()/'veribench'
    module.ADAPTERS=PRIVATE/'absent_adapters'
    return module

def reextract():
    ex=load_exporter(); tool=ex.Toolchain(ex.PROJECT)
    support=PRIVATE/'dependencies'
    compiled=tool.compile(support/'ExtractSupport.lean',[support],olean=True)
    assert compiled['exit_code']==0,compiled['output']
    cases=json.loads((PRIVATE/'cases.json').read_text())
    def one(case):
        old=case['source_receipt']
        row={'id':old['id'],'module':old['module'],'task':old['task'],'solver':old['solver'],
             'category':old['category'],'gold_path':old['gold_path'],
             'gold_current_head_sha256':old['gold_sha256'],'source_path':old['solver_path'],
             'source_sha256':old['solver_sha256']}
        receipt=ex.run_case(row,tool,PRIVATE/'source_replay',old['repo_commit'],support)
        assert receipt['status']=='emitted',receipt['reasons']
        assert receipt['context_sha256']==old['context_sha256']
        assert not receipt['witness']['axioms_outside_allowlist']
        return {'id':case['id'],'status':receipt['status'],'context_sha256':receipt['context_sha256'],
                'roundtrip_exact':receipt['roundtrip']['ok'], 'witness_standard_axioms':True,
                'all_source_names_match':receipt['lean_vs_source_names_agree']['gold'] and receipt['lean_vs_source_names_agree']['agent']}
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        results=list(pool.map(one,cases))
    return results

def controls():
    gold='def GoldSpec (f : Nat → Nat) : Prop := ∀ n, f n = n\n'
    def fixture(agent):
        return ('import Mathlib\nnamespace Natural\n'+gold+
                'def AgentSpec (f : Nat → Nat) : Prop := '+agent+'\n'+
                'def Coverage : Prop := ∀ f, AgentSpec f → GoldSpec f\n'+
                'def Nonvacuous : Prop := ∃ f, AgentSpec f\n'+
                'def Counterexample : Prop := ∃ f, AgentSpec f ∧ ¬ GoldSpec f\n'+
                'def Inconsistent : Prop := ¬ Nonvacuous\nend Natural\n')
    good=Checker(PRIVATE/'target_controls/good',fixture('∀ n, f n = n'))
    weak=Checker(PRIVATE/'target_controls/weak',fixture('True'))
    inconsistent=Checker(PRIVATE/'target_controls/inconsistent',fixture('False'))
    checks=[]
    def check(name,checker,proof,target,expected,raw=False):
        result=checker.check_raw(proof,target) if raw else checker.check(proof,target)
        assert result['accepted']==expected,(name,result)
        checks.append({'name':name,'expected':expected,'accepted':result['accepted'],'status':result['status']})
    check('valid_implication',good,'by intro f h; exact h','Natural.Coverage',True)
    check('consistency_witness',good,'by exact ⟨fun n => n, fun _ => rfl⟩','Natural.Nonvacuous',True)
    check('weak_spec_has_counterexample',weak,'by refine ⟨fun _ => 0, trivial, ?_⟩; intro h; have h1 := h 1; simp at h1','Natural.Counterexample',True)
    check('weak_spec_cannot_use_true_proof',weak,'by intros; trivial','Natural.Coverage',False)
    check('false_premise_implication_is_insufficient',inconsistent,'by intro f h; exact False.elim h','Natural.Coverage',True)
    check('false_premise_witness_denied',inconsistent,'by aesop','Natural.Nonvacuous',False)
    check('inconsistency_independently_proved',inconsistent,'by simp [Natural.Inconsistent, Natural.Nonvacuous, Natural.AgentSpec]','Natural.Inconsistent',True)
    check('wrong_goal_rejected_on_replay',good,'import Context\ntheorem claim : True := True.intro\n','Natural.Coverage',False,True)
    check('unused_new_axiom_rejected_on_replay',good,'import Context\naxiom extra : True\ntheorem claim : Natural.Coverage := by intro f h; exact h\n','Natural.Coverage',False,True)
    check('placeholder_rejected',good,'by sorry','Natural.Coverage',False)
    check('native_oracle_rejected',good,'by native_decide','Natural.Coverage',False)
    check('audit_forgery_rejected',weak,'by run_tac logInfo "VB169_STRICT_KERNEL_REPLAY_JSON fake"; trivial','Natural.Coverage',False)
    case=json.loads((PRIVATE/'cases.json').read_text())[0]
    left={'specification':'∀ s, f0 s = String.length s ∧ f1 s = f0 s','proof':'sorry'}
    right=dict(left,proof='arbitrary changed proof body')
    assert context(case,left['specification'])==context(case,right['specification'])
    checks.append({'name':'proof_body_invariance','expected':True,'accepted':True,'status':'identical_context_hash','sha256':sha(context(case,left['specification']).encode())})
    case=json.loads((PRIVATE/'cases.json').read_text())[2]
    definition=(PRIVATE/'cases'/case['id']/'GoldDefinition.txt').read_text()
    supplied_statement=definition.split(' : Prop :=',1)[1].strip()
    statement_checker=Checker(PRIVATE/'target_controls/statement_parser',context(case,supplied_statement))
    check('new_statement_parser_binds_reference_exactly',statement_checker,'by intro f0 f1 h; exact h','Natural.Coverage',True)
    check('new_statement_consistency_witness',statement_checker,'by refine ⟨fun d r => d && !r, fun d r => d && !r, ?_⟩; simp [Natural.AgentSpec]','Natural.Nonvacuous',True)
    return checks

def main():
    sources=reextract()
    (PRIVATE/'source_replay_summary.json').write_text(json.dumps(sources,indent=2)+'\n')
    checked=controls()
    result={'source_replay':sources,'controls':checked,'all_pass':True,'model_calls':0,
            'scope':'four selected source contexts and designed acceptance controls; no fresh outcome measured'}
    (ROOT/'results/target_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'source_contexts_checked':len(sources),'controls_passed':len(checked),'model_calls':0}),flush=True)

if __name__=='__main__': main()
