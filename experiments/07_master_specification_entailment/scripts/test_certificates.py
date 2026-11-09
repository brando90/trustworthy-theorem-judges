#!/usr/bin/env python3
"""Deterministic attack and construction checks; no model inference."""
from collections import Counter, defaultdict
import json
import os
from pathlib import Path
import tempfile
import unittest
from build_controls import ROOT, create_cases, dump, sha
from certificate_checker import CertificateChecker


class ConstructionTests(unittest.TestCase):
    def test_deterministic_public_statements(self):
        cases, inputs = create_cases()
        self.assertEqual((cases, inputs), create_cases())
        self.assertEqual(len(cases), 48)
        self.assertEqual(len(set(x['id'] for x in inputs)), 48)
        self.assertEqual({tuple(sorted(x)) for x in inputs}, {('id', 'statement')})
        for case, item in zip(cases, inputs, strict=True):
            self.assertEqual(case['statement_sha256'], sha(item['statement']))
            for hidden in ['certificate', 'Counterexample', 'Nonvacuous', 'proof_body',
                           'oracle', 'wrong_goal', 'TTJ07_CERTIFICATE_AUDIT', case['family']]:
                self.assertNotIn(hidden, item['statement'])

    def test_family_splits_and_invariance(self):
        cases, inputs = create_cases()
        by_id = {x['id']: x for x in inputs}
        families = defaultdict(list)
        for case in cases:
            families[case['family']].append(case)
        self.assertEqual(len(families), 6)
        self.assertEqual(Counter(c['split'] for c in cases), {'train': 16, 'validation': 16, 'test': 16})
        for cases_in_family in families.values():
            self.assertEqual(len({x['split'] for x in cases_in_family}), 1)
            self.assertEqual(Counter(str(c['predicted_label']) for c in cases_in_family), {'1': 3, '0': 3, 'None': 2})
            indexed = {x['control_type']: x for x in cases_in_family}
            a, b = indexed['oracle'], indexed['proof_body_variant']
            self.assertNotEqual(a['supplied_proof_body'], b['supplied_proof_body'])
            self.assertNotEqual(a['proofs'], b['proofs'])
            self.assertEqual(by_id[a['id']]['statement'], by_id[b['id']]['statement'])
        # The family split implies no equal statement crosses train/validation/test.
        memberships = defaultdict(set)
        for c in cases:
            memberships[c['statement_sha256']].add(c['split'])
        self.assertTrue(all(len(s) == 1 for s in memberships.values()))


class KernelCheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.checker = CertificateChecker()
        cls.tmp = tempfile.TemporaryDirectory(prefix='ttj07_checker_')
        cls.directory = Path(cls.tmp.name)
        cls.statement = create_cases()[1][0]['statement']
        cls.receipts = []

    @classmethod
    def tearDownClass(cls):
        output = Path(os.environ.get('TTJ07_CHECKER_TEST_OUTPUT', str(ROOT / 'results/checker_tests.json')))
        if (ROOT / 'inference_freeze.json').exists() and output.is_relative_to(ROOT):
            output = Path(tempfile.mkdtemp(prefix='ttj07_tests_')) / 'checker_tests.json'
        dump(output, {'pins': cls.checker.pins,
             'tests': cls.receipts, 'all_expected_outcomes_observed': all(r['matched'] for r in cls.receipts)})
        cls.tmp.cleanup()

    def check_raw(self, name, raw, accepted, target='Coverage'):
        result = self.checker.check(self.statement, {}, self.directory / (name + '.lean'),
                                    raw=raw, audit_target=target)
        matched = result['accepted'] == accepted
        self.receipts.append({'name': name, 'expected_accepted': accepted, 'matched': matched, 'result': result})
        self.assertTrue(matched, result)
        return result

    def test_exact_goal_and_kernel_replay(self):
        result = self.check_raw('exact_goal', 'theorem claim : Coverage := by intro f h; exact h', True)
        self.assertEqual(len(result['audit_records']), 1)
        self.assertTrue(result['audit_records'][0]['kernel_replayed'])

    def test_wrong_goal_is_rejected(self):
        result = self.check_raw('wrong_goal', 'theorem claim : True := True.intro', False)
        self.assertIn('wrong exact goal', result['compile']['output'])

    def test_transitive_axiom_is_rejected(self):
        result = self.check_raw('transitive_axiom',
            'axiom hidden : Coverage\ntheorem middle : Coverage := hidden\ntheorem claim : Coverage := middle', False)
        self.assertIn('Forbidden transitive axiom: hidden', result['compile']['output'])

    def test_sorry_axiom_is_rejected(self):
        result = self.check_raw('sorry_axiom', 'theorem claim : Coverage := by sorry', False)
        self.assertIn('Forbidden transitive axiom: sorryAx', result['compile']['output'])

    def test_forged_audit_string_is_rejected(self):
        forged = 'TTJ07_CERTIFICATE_AUDIT ' + json.dumps({'nonce': 'forged', 'claim': 'claim',
                 'exact_goal': True, 'kernel_replayed': True, 'axioms': []})
        result = self.check_raw('forged_audit', '#eval IO.println ' + json.dumps(forged)
                                + '\ntheorem claim : True := True.intro', False)
        self.assertEqual(result['audit_records'], [])

    def test_term_parser_rejects_command_injection(self):
        proof = 'by exact (fun f h => h)\naxiom injected : False'
        result = self.check_raw('term_injection', 'certificate claim : Coverage := ' + json.dumps(proof), False)
        self.assertIn('Expected exactly one proof term', result['compile']['output'])

    def test_lexical_guard_is_additional_only(self):
        result = self.checker.check(self.statement, {'Coverage': 'by sorry'}, self.directory / 'guard.lean')
        self.assertFalse(result['accepted'])
        self.assertEqual(result['status'], 'proof_guard_rejected')
        self.receipts.append({'name': 'lexical_guard', 'expected_accepted': False, 'matched': True, 'result': result})


if __name__ == '__main__':
    unittest.main()
