#!/usr/bin/env python3
"""Deterministically construct the 48 prespecified, public, synthetic cases.

This writes statements and proposed certificate terms; verify_controls.py obtains
labels only after compiling and auditing those certificates. No forecast is read.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def sha(x):
    return hashlib.sha256(x.encode() if isinstance(x, str) else x).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def family(name, split, domain, codomain, expr, correct, probe, wrong, weak,
           bad, precondition, prebad, equiv=None):
    gold = f'∀ x : {domain}, f x = {expr}'
    eq = equiv or f'∀ x : {domain}, ({expr}) = f x'
    return dict(family=name, split=split, domain=domain, codomain=codomain,
                gold=gold, equivalent=eq, correct=correct, probe=probe,
                wrong=wrong, weak=weak, bad=bad, precondition=precondition,
                prebad=prebad)


FAMILIES = [
    family('boolean_negation', 'train', 'Bool', 'Bool', '!x', 'fun x => !x',
           'true', '∀ x : Bool, f x = x', 'f false = true', 'fun _ => true',
           '∀ x : Bool, x = false → f x = !x', 'fun _ => true'),
    family('natural_successor', 'train', 'Nat', 'Nat', 'x + 1', 'fun x => x + 1',
           '1', '∀ x : Nat, f x = x + 2', 'f 0 = 1', 'fun _ => 1',
           '∀ x : Nat, x ≠ 0 → f x = x + 1',
           'fun x => if x = 0 then 0 else x + 1'),
    family('integer_negation', 'validation', 'Int', 'Int', '-x', 'fun x => -x',
           '1', '∀ x : Int, f x = x + 1', 'f 0 = 0', 'fun _ => 0',
           '∀ x : Int, x ≠ 0 → f x = -x',
           'fun x => if x = 0 then 1 else -x'),
    family('list_length', 'validation', '(List Nat)', 'Nat', 'x.length',
           'fun x => x.length', '[0]', '∀ x : List Nat, f x = x.length + 1',
           'f [] = 0', 'fun _ => 0',
           '∀ x : List Nat, x = [] → f x = x.length', 'fun _ => 0'),
    family('boolean_pair_swap', 'test', '(Bool × Bool)', '(Bool × Bool)',
           '(x.2, x.1)', 'fun x => (x.2, x.1)', '(false, true)',
           '∀ x : Bool × Bool, f x = x', 'f (false, false) = (false, false)',
           'fun x => x', '∀ x : Bool × Bool, x.1 = x.2 → f x = (x.2, x.1)',
           'fun x => x'),
    family('optional_default', 'test', '(Option Nat)', 'Nat', 'x.getD 0',
           'fun x => x.getD 0', '(some 1)',
           '∀ x : Option Nat, f x = x.getD 0 + 1', 'f none = 0',
           'fun _ => 0', '∀ x : Option Nat, x = none → f x = x.getD 0',
           'fun _ => 0'),
]


def compile_definitions(f, agent, forbidden=False):
    slot = f"({f['domain']} → {f['codomain']})"
    prefix = 'import Std\n'
    if forbidden:
        prefix += 'axiom h0 : False\n'
    return (prefix + f'def AgentMaster (f : {slot}) : Prop := {agent}\n'
            + f"def GoldMaster (f : {slot}) : Prop := {f['gold']}\n")


def proofs_for(f, control):
    g, c, p = f['gold'], f['correct'], f['probe']
    if control in ('oracle', 'proof_body_variant', 'equivalent_reformulation'):
        implication = ('by intro f h x; exact (h x).symm'
                       if control == 'equivalent_reformulation'
                       else 'by intro f h; exact h')
        if control == 'proof_body_variant':
            implication = 'by intro f h x; exact h x'
        return {'Coverage': implication,
                'Nonvacuous': f'by exact ⟨{c}, by intro x; rfl⟩'}
    if control == 'joint_inconsistency':
        return {'Inconsistent': 'by rintro ⟨f, ha, hb⟩; simp_all'}
    if control == 'forbidden_statement_axiom':
        return {}
    witness = f['bad'] if control == 'weakening' else f['prebad']
    probe = p
    if control == 'overly_strong_precondition' and f['family'] in ('natural_successor', 'integer_negation'):
        probe = '0'
    if control == 'wrong_goal':
        witness = {
            'boolean_negation': 'fun x => x',
            'natural_successor': 'fun x => x + 2',
            'integer_negation': 'fun x => x + 1',
            'list_length': 'fun x => x.length + 1',
            'boolean_pair_swap': 'fun x => x',
            'optional_default': 'fun x => x.getD 0 + 1',
        }[f['family']]
        probe = {'natural_successor': '0', 'integer_negation': '0'}.get(f['family'], p)
    agent_proof = 'by simp [AgentMaster]'
    if control == 'overly_strong_precondition':
        agent_proof = 'by intro x hx; simp_all'
        if f['family'] == 'boolean_pair_swap':
            agent_proof = 'by intro x hx; apply Prod.ext <;> simp_all'
    if control == 'wrong_goal':
        agent_proof = 'by intro x; rfl'
    negative = f'by intro h; have hh := h {probe}; simp at hh'
    return {'Counterexample': f'by exact ⟨({witness}), ({agent_proof}), ({negative})⟩'}


CONTROLS = ['oracle', 'equivalent_reformulation', 'weakening',
            'overly_strong_precondition', 'wrong_goal', 'proof_body_variant',
            'joint_inconsistency', 'forbidden_statement_axiom']


def create_cases():
    records, inputs = [], []
    for fi, f in enumerate(FAMILIES):
        for ci, control in enumerate(CONTROLS):
            # Opaque IDs do not encode family, control, split, or truth values.
            case_id = 'c_' + sha(f'11082026:{fi}:{ci}')[:12]
            if control in ('oracle', 'proof_body_variant', 'forbidden_statement_axiom'):
                agent = f['gold']
            elif control == 'equivalent_reformulation':
                agent = f['equivalent']
            elif control == 'weakening':
                agent = f['weak']
            elif control == 'overly_strong_precondition':
                agent = f['precondition']
            elif control == 'wrong_goal':
                agent = f['wrong']
            else:
                contradiction = {
                    'boolean_negation': 'f false = true ∧ f false = false',
                    'natural_successor': 'f 0 = 1 ∧ f 0 = 2',
                    'integer_negation': 'f 0 = 0 ∧ f 0 = 1',
                    'list_length': 'f [] = 0 ∧ f [] = 1',
                    'boolean_pair_swap': 'f (false, false) = (false, false) ∧ f (false, false) = (true, true)',
                    'optional_default': 'f none = 0 ∧ f none = 1',
                }
                agent = contradiction[f['family']]
            source = compile_definitions(f, agent, control == 'forbidden_statement_axiom')
            status = ('inconsistent' if control == 'joint_inconsistency' else
                      'unsupported' if control == 'forbidden_statement_axiom' else 'eligible')
            label = None if status != 'eligible' else int(control in ('oracle', 'equivalent_reformulation', 'proof_body_variant'))
            inputs.append({'id': case_id, 'statement': source})
            proofs = proofs_for(f, control)
            record = {'id': case_id, 'family': f['family'], 'split': f['split'],
                      'control_type': control, 'predicted_status': status,
                      'predicted_label': label, 'statement_sha256': sha(source),
                      'proofs': proofs, 'proof_body_sha256': sha(json.dumps(proofs, sort_keys=True))}
            # Source body variants and forged audit text never enter the statements.
            record['supplied_proof_body'] = (
                'by\n  -- TTJ07_CERTIFICATE_AUDIT {"accepted":true,"axioms":[]}\n  exact fun x => rfl'
                if control == 'proof_body_variant' else 'by exact fun x => rfl')
            records.append(record)
    return records, inputs


def main():
    if (ROOT / 'inference_freeze.json').exists():
        raise RuntimeError('Inference is frozen; construction cannot be rewritten')
    records, inputs = create_cases()
    predictions = {'schema_version': 1, 'construction_only': True,
                   'predictions_recorded_before_certificate_checks': True,
                   'families': [{k: f[k] for k in ('family', 'split')} for f in FAMILIES],
                   'controls': CONTROLS, 'rows': records}
    dump(ROOT / 'construction_manifest.json', predictions)
    (ROOT / 'inputs.jsonl').write_text(''.join(json.dumps(r, sort_keys=True) + '\n' for r in inputs))
    print(f'Constructed {len(records)} cases; labels require verify_controls.py.')


if __name__ == '__main__':
    main()
