#!/usr/bin/env python3
"""Prospective outcome-level wrapper around CertificateChecker.

Preserves frozen scripts/certificate_checker.py and inference_freeze.json unchanged
while enforcing exact, non-empty target sets for prospective callers:
- 'positive': {'Coverage', 'Nonvacuous'}
- 'negative': {'Counterexample'}
- 'inconsistent': {'Inconsistent'}
Unsupported or unknown outcomes remain ineligible and are rejected before kernel replay.
Trust boundary remains identical to CertificateChecker (trusted specification construction
and pinned Lean toolchain; not a sandbox for arbitrary hostile Lean plugins/native code).
"""
from certificate_checker import CertificateChecker

REQUIRED_TARGETS = {
    'positive': frozenset({'Coverage', 'Nonvacuous'}),
    'negative': frozenset({'Counterexample'}),
    'inconsistent': frozenset({'Inconsistent'}),
}


class OutcomeCertificateChecker:
    def __init__(self, lean=None, checker=None):
        self.checker = checker or CertificateChecker(lean=lean)
        self.pins = self.checker.pins

    def check_outcome(self, outcome, statement, proofs, path, *, nonce=None, write=True):
        if outcome not in REQUIRED_TARGETS:
            return {
                'accepted': False,
                'status': 'ineligible_outcome',
                'outcome': outcome,
                'targets': [],
            }
        if not isinstance(proofs, dict) or len(proofs) == 0:
            return {
                'accepted': False,
                'status': 'empty_proof_targets',
                'outcome': outcome,
                'targets': [],
            }
        expected = REQUIRED_TARGETS[outcome]
        supplied = frozenset(proofs.keys())
        if supplied != expected:
            return {
                'accepted': False,
                'status': 'wrong_proof_targets',
                'outcome': outcome,
                'expected_targets': sorted(expected),
                'targets': sorted(str(k) for k in proofs.keys()),
            }
        result = self.checker.check(statement, proofs, path, nonce=nonce, write=write)
        records = result.get('audit_records', [])
        expected_claims = frozenset('claim_' + t for t in expected)
        exact_targets = (
            frozenset(result.get('targets', ())) == expected
            and len(records) == len(expected)
            and frozenset(r.get('claim') for r in records) == expected_claims
        )
        accepted = bool(result.get('accepted')) and exact_targets
        out = dict(result)
        out['outcome'] = outcome
        out['accepted'] = accepted
        if not accepted and result.get('accepted'):
            out['status'] = 'incomplete_target_audits'
        return out
