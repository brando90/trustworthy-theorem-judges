#!/usr/bin/env python3
"""Deterministic tests for the prospective OutcomeCertificateChecker wrapper."""
from pathlib import Path
import tempfile
import unittest
from build_controls import create_cases
from outcome_checker import OutcomeCertificateChecker


class OutcomeCheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.outcome_checker = OutcomeCertificateChecker()
        cls.tmp = tempfile.TemporaryDirectory(prefix='ttj07_outcome_checker_')
        cls.directory = Path(cls.tmp.name)
        cases, inputs = create_cases()
        by_id = {row['id']: row['statement'] for row in inputs}
        cls.positive_case = next(c for c in cases if c['control_type'] == 'oracle')
        cls.negative_case = next(c for c in cases if c['control_type'] == 'weakening')
        cls.inconsistent_case = next(c for c in cases if c['control_type'] == 'joint_inconsistency')
        cls.unsupported_case = next(c for c in cases if c['control_type'] == 'forbidden_statement_axiom')
        cls.by_id = by_id

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_rejects_empty_proof_mapping(self):
        stmt = self.by_id[self.positive_case['id']]
        res = self.outcome_checker.check_outcome(
            'positive', stmt, {}, self.directory / 'empty.lean'
        )
        self.assertFalse(res['accepted'])
        self.assertEqual(res['status'], 'empty_proof_targets')

    def test_rejects_missing_or_mismatched_target_sets(self):
        stmt = self.by_id[self.positive_case['id']]
        only_cov = {'Coverage': self.positive_case['proofs']['Coverage']}
        res_missing = self.outcome_checker.check_outcome(
            'positive', stmt, only_cov, self.directory / 'missing_nonvacuous.lean'
        )
        self.assertFalse(res_missing['accepted'])
        self.assertEqual(res_missing['status'], 'wrong_proof_targets')
        self.assertEqual(res_missing['expected_targets'], ['Coverage', 'Nonvacuous'])

        res_wrong_outcome = self.outcome_checker.check_outcome(
            'negative', stmt, self.positive_case['proofs'], self.directory / 'wrong_outcome.lean'
        )
        self.assertFalse(res_wrong_outcome['accepted'])
        self.assertEqual(res_wrong_outcome['status'], 'wrong_proof_targets')
        self.assertEqual(res_wrong_outcome['expected_targets'], ['Counterexample'])

    def test_rejects_unsupported_and_unknown_outcomes(self):
        stmt = self.by_id[self.unsupported_case['id']]
        res_unsupported = self.outcome_checker.check_outcome(
            'unsupported', stmt, {}, self.directory / 'unsupported.lean'
        )
        self.assertFalse(res_unsupported['accepted'])
        self.assertEqual(res_unsupported['status'], 'ineligible_outcome')

        res_unknown = self.outcome_checker.check_outcome(
            'unknown', stmt, self.positive_case['proofs'], self.directory / 'unknown.lean'
        )
        self.assertFalse(res_unknown['accepted'])
        self.assertEqual(res_unknown['status'], 'ineligible_outcome')

    def test_accepts_valid_positive_negative_and_inconsistent_controls(self):
        pos_stmt = self.by_id[self.positive_case['id']]
        res_pos = self.outcome_checker.check_outcome(
            'positive', pos_stmt, self.positive_case['proofs'], self.directory / 'valid_pos.lean'
        )
        self.assertTrue(res_pos['accepted'], res_pos)
        self.assertEqual(len(res_pos['audit_records']), 2)
        self.assertEqual({r['claim'] for r in res_pos['audit_records']}, {'claim_Coverage', 'claim_Nonvacuous'})

        neg_stmt = self.by_id[self.negative_case['id']]
        res_neg = self.outcome_checker.check_outcome(
            'negative', neg_stmt, self.negative_case['proofs'], self.directory / 'valid_neg.lean'
        )
        self.assertTrue(res_neg['accepted'], res_neg)
        self.assertEqual(len(res_neg['audit_records']), 1)
        self.assertEqual({r['claim'] for r in res_neg['audit_records']}, {'claim_Counterexample'})

        inc_stmt = self.by_id[self.inconsistent_case['id']]
        res_inc = self.outcome_checker.check_outcome(
            'inconsistent', inc_stmt, self.inconsistent_case['proofs'], self.directory / 'valid_inc.lean'
        )
        self.assertTrue(res_inc['accepted'], res_inc)
        self.assertEqual(len(res_inc['audit_records']), 1)
        self.assertEqual({r['claim'] for r in res_inc['audit_records']}, {'claim_Inconsistent'})


if __name__ == '__main__':
    unittest.main()
