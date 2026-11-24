#!/usr/bin/env python3
"""Unit tests for Experiment 26 analysis helpers and provenance invariants."""
from __future__ import annotations

import sys
import unittest
import json
from fractions import Fraction
from pathlib import Path
from unittest import mock

import numpy as np
from scipy import stats

EXP26_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(EXP26_DIR / "scripts"))

import analyze_old_and_new_ratings as mod  # noqa: E402


class TestAnalyzeOldAndNewRatings(unittest.TestCase):
    def test_pmf_helpers_preserve_mass_and_expectation(self) -> None:
        for val in (0.0, 1.25, 2.5, 4.0, 5.0):
            q = mod.linear_interp_pmf(val)
            self.assertEqual(q.shape, (6,))
            self.assertAlmostEqual(float(q.sum()), 1.0, places=12)
            self.assertAlmostEqual(float(q @ mod.e5.GRID), val / 5.0, places=12)
            self.assertTrue(np.all(q >= 0.0))

        oh = mod.one_hot_pmf(3)
        self.assertEqual(list(oh), [0.0, 0.0, 0.0, 1.0, 0.0, 0.0])
        sm = mod.smooth_pmf(oh, eps=1e-3)
        self.assertAlmostEqual(float(sm.sum()), 1.0, places=12)
        self.assertTrue(np.all(sm >= 1e-3 / 1.005 - 1e-12))

    def test_count_theorems_comments_strings_and_visibility(self) -> None:
        lean_src = """
-- theorem commented_out : True := trivial
/-
nested /- theorem inside_nested : True := trivial -/
lemma inside_block : True := trivial
-/
def s := "theorem inside_string \\"still string\\" lemma nope"
@[simp] theorem pub_thm : True := trivial
  private lemma priv_lem : True := trivial
protected theorem prot_thm : True := trivial
noncomputable lemma noncomp_lem : True := trivial
"""
        self.assertEqual(mod.count_theorems(lean_src, public_only=False), 4)
        self.assertEqual(mod.count_theorems(lean_src, public_only=True), 2)

    def test_count_theorems_handles_lean_char_literals_and_identifier_primes(self) -> None:
        lean_src = """
def dq : Char := '"'
def sq : Char := '\\''
def hex : Char := '\\x22'
theorem foo' (x' y' : Nat) : x' = y' := sorry
private lemma priv_after_char : True := trivial
theorem bar_after_char : True := trivial
"""
        self.assertEqual(mod.count_theorems(lean_src, public_only=False), 3)
        self.assertEqual(mod.count_theorems(lean_src, public_only=True), 2)

    def test_synthetic_metric_identities(self) -> None:
        P = np.array([
            [1.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            [0.0, 0.0, 0.0, 0.0, 0.0, 1.0],
        ])
        Q_opp = np.array([
            [0.0, 0.0, 0.0, 0.0, 0.0, 1.0],
            [1.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        ])
        rps_exact, cdf_exact, _ = mod.e5.rps_components(P, P)
        self.assertTrue(np.allclose(rps_exact, 0.0))
        self.assertTrue(np.allclose(cdf_exact, 0.0))
        self.assertTrue(np.allclose(mod.e5.tvd_per_artifact(P, P), 0.0))

        rps_opp, _, _ = mod.e5.rps_components(P, Q_opp)
        self.assertTrue(np.allclose(rps_opp, 1.0))
        self.assertTrue(np.allclose(mod.e5.tvd_per_artifact(P, Q_opp), 1.0))

        ce_self = mod.e5.ce_per_artifact(P, np.array([[0.5, 0.5, 0.0, 0.0, 0.0, 0.0], [0.0, 0.0, 0.0, 0.0, 0.5, 0.5]]))
        self.assertTrue(np.allclose(ce_self, np.log(2.0)))

        agr_same = mod.weighted_kappas_and_agreement([0, 2, 4, 5], [0, 2, 4, 5])
        self.assertEqual(agr_same["exact_match"], 1.0)
        self.assertEqual(agr_same["within_1"], 1.0)
        self.assertAlmostEqual(agr_same["kappa_linear"], 1.0, places=12)
        self.assertAlmostEqual(agr_same["kappa_quadratic"], 1.0, places=12)

    def test_simpsons_paradox_constant_within_regime_positive_pooled(self) -> None:
        # Two regimes with zero within-regime variance in predictions, undefined correlation,
        # yet pooling induces strong positive correlation from between-regime mean shift.
        rng = np.random.default_rng(7)
        P_old = np.vstack([mod.one_hot_pmf(int(rng.choice([4, 5]))) for _ in range(20)])
        P_new = np.vstack([mod.one_hot_pmf(int(rng.choice([0, 1]))) for _ in range(20)])
        Q_old = np.broadcast_to(P_old.mean(axis=0), (20, 6)).copy()
        Q_new = np.broadcast_to(P_new.mean(axis=0), (20, 6)).copy()

        P_pool = np.vstack([P_old, P_new])
        Q_pool = np.vstack([Q_old, Q_new])
        Q_global = np.broadcast_to(P_pool.mean(axis=0), (40, 6)).copy()
        tasks = np.array([f"t{i // 4}" for i in range(40)])

        boot = mod.task_cluster_bootstrap(P_pool, Q_pool, tasks, draws=200, seed=11, baseline_Q_raw=Q_global)
        self.assertGreater(boot["point"]["pearson"], 0.85)
        self.assertGreater(boot["point"]["spearman"], 0.85)
        self.assertLess(boot["paired_minus_baseline"]["rps"]["diff_point"], -0.1)

    def test_pooling_reports_undefined_within_cohort_correlations(self) -> None:
        dataset = {"rows": [
            {"task": "old1", "ratings": [0]},
            {"task": "old2", "ratings": [1]},
        ]}
        new_ratings = np.vstack([mod.one_hot_pmf(4), mod.one_hot_pmf(5)])
        with mock.patch.object(mod, "_load_old_dataset", return_value=dataset), mock.patch.object(mod, "BOOT_DRAWS", 20):
            result = mod._compute_simpson_pooling(new_ratings, np.array(["new1", "new2"]))
        self.assertIsNone(result["within_old_correlation"])
        self.assertIsNone(result["within_new_correlation"])
        self.assertGreater(result["pooled_metrics"]["pearson"]["point"], 0.9)

    def test_assert_no_private_leak(self) -> None:
        mod.assert_no_private_leak({"ok": [1, {"nested_count": 2}]})
        for bad_key in ("sealed", "ratings", "per_item", "agent_map"):
            with self.assertRaises(AssertionError):
                mod.assert_no_private_leak({"outer": {bad_key: [1, 2, 3]}})

    def test_canonical_exp09_item_id_join_preserves_t06_anomaly(self) -> None:
        catalog, rows = mod.load_canonical_exp09()
        self.assertEqual(len(catalog), 100)
        t06_item20 = [
            r for r in rows
            if r["rater_id"].strip() == "T06" and r["item_id"].strip() == "native-heavy-11-11-2026__item020"
        ]
        self.assertEqual(len(t06_item20), 1)
        row = t06_item20[0]
        self.assertFalse(row["_candidate_file_matches_canonical"])
        self.assertEqual(row["candidate_file"].strip(), "this one has borderline spam.")
        self.assertEqual(row["_canonical_task"], catalog["native-heavy-11-11-2026__item020"]["task_folder"])
        self.assertTrue(row["_canonical_cand"].endswith(".lean"))

    def test_vectorized_correlations_match_scalar_references(self) -> None:
        xs_rows = [
            [0.1, 0.4, 0.2, 0.9, 0.5, 0.7, 0.3],
            [1.0, 1.0, 2.0, 2.0, 3.0, 5.0, 5.0],
            [2.0, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0],
        ]
        ys_rows = [
            [0.2, 0.3, 0.5, 0.8, 0.4, 0.9, 0.1],
            [3.0, 2.0, 2.0, 4.0, 1.0, 5.0, 5.0],
            [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0],
        ]
        X = np.asarray(xs_rows, dtype=float)
        Y = np.asarray(ys_rows, dtype=float)
        vp = mod._batch_pearson(X, Y)
        vs = mod._batch_spearman(X, Y)
        vk = mod._batch_kendall_tau_b(X, Y)

        for row_i, (xs, ys) in enumerate(zip(xs_rows, ys_rows)):
            ref_p = mod._clean_float(mod.e5.safe_correlations(np.asarray(xs), np.asarray(ys))["pearson"])
            if ref_p is not None:
                ref_s = stats.spearmanr(xs, ys).statistic
                ref_k = stats.kendalltau(xs, ys).statistic
            if ref_p is None:
                self.assertTrue(np.isnan(vp[row_i]))
                self.assertTrue(np.isnan(vs[row_i]))
                self.assertTrue(np.isnan(vk[row_i]))
            else:
                self.assertAlmostEqual(float(vp[row_i]), ref_p, places=12)
                self.assertAlmostEqual(float(vs[row_i]), ref_s, places=12)
                self.assertAlmostEqual(float(vk[row_i]), ref_k, places=12)

    def test_constant_decimal_correlations_remain_undefined(self) -> None:
        # Decimal centering can leave a nonzero residual even for a constant row.
        X = np.array([[0.1, 0.1, 0.1]])
        Y = np.array([[0.1, 0.1, 0.1]])
        self.assertTrue(np.isnan(mod._batch_pearson(X, Y)[0]))
        for method in ("pearson", "spearman", "kendall"):
            result = mod._corr_ci_perm(X[0].tolist(), Y[0].tolist(), method, draws=20)
            self.assertIsNone(result["value"])
            self.assertIsNone(result["ci95"])

    def test_kappa_undefined_for_equal_constant_raters(self) -> None:
        agreement = mod.weighted_kappas_and_agreement([5, 5], [5, 5])
        self.assertEqual(agreement["exact_match"], 1.0)
        self.assertEqual(agreement["within_1"], 1.0)
        self.assertIsNone(agreement["kappa_linear"])
        self.assertIsNone(agreement["kappa_quadratic"])
        for a, b in (([], []), ([1], [1, 2]), ([-1], [1]), ([0.5], [1])):
            with self.assertRaises(ValueError):
                mod.weighted_kappas_and_agreement(a, b)

    def test_laplace_smooth_counts_uses_actual_repeat_count(self) -> None:
        c1 = np.array([1.0, 0.0, 0.0, 0.0, 0.0, 0.0])  # 1 repeat
        c2 = np.array([0.0, 0.0, 1.0, 1.0, 0.0, 0.0])  # 2 repeats
        Q = mod.laplace_smooth_counts([c1, c2], alpha=0.5)
        self.assertAlmostEqual(float(Q[0, 0]), 1.5 / 4.0, places=12)
        self.assertAlmostEqual(float(Q[0, 1]), 0.5 / 4.0, places=12)
        self.assertAlmostEqual(float(Q[1, 2]), 1.5 / 5.0, places=12)
        self.assertAlmostEqual(float(Q[1, 0]), 0.5 / 5.0, places=12)

    def test_exact_tvd_preserves_ties_across_counts_and_order(self) -> None:
        p = np.array([1, 1, 1, 1, 1, 0])
        q = np.array([1, 1, 1, 0, 0, 0])
        first = mod._exact_tvd_from_counts(p, q)
        second = mod._exact_tvd_from_counts(p[::-1] * 2, q[::-1] * 3)
        self.assertEqual(first, Fraction(2, 5))
        self.assertEqual(first, second)
        self.assertEqual(float(first), float(second))
        for invalid in (np.zeros(6), np.array([0.5] * 6), np.array([-1, 2, 0, 0, 0, 0])):
            with self.assertRaises(ValueError):
                mod._exact_tvd_from_counts(invalid, q)

    def test_artifact_metrics_laplace_respects_effective_counts(self) -> None:
        P = np.tile(np.array([0.0, 0.0, 0.0, 0.0, 0.2, 0.8]), (100, 1))
        Q_const = np.tile(np.array([0.0, 0.0, 0.0, 0.0, 0.2, 0.8]), (100, 1))
        vecs_n100 = mod._artifact_metric_vectors(P, Q_const, Q_counts=100.0 * Q_const)
        vecs_det = mod._artifact_metric_vectors(P, np.tile(mod.linear_interp_pmf(5.0), (100, 1)))
        expected_lap = -(0.2 * np.log(20.5 / 103.0) + 0.8 * np.log(80.5 / 103.0))
        self.assertAlmostEqual(float(vecs_n100["ce_laplace05"].mean()), float(expected_lap), places=12)
        self.assertLess(float(vecs_n100["ce_laplace05"].mean()), float(vecs_det["ce_laplace05"].mean()))
        self.assertLess(abs(float(vecs_n100["ce_laplace05"].mean()) - float(vecs_n100["ce_eps1e6"].mean())), 0.025)

    def test_compute_loro_ceiling_synthetic(self) -> None:
        catalog = {
            "i1": {"task_folder": "t1", "candidate_file": "a.lean"},
            "i2": {"task_folder": "t2", "candidate_file": "b.lean"},
        }
        by_item = {
            "i1": [("R1", 5), ("R2", 5)],
            "i2": [("R1", 5), ("R2", 4)],
        }
        loro = mod._compute_loro_ceiling(catalog, by_item)
        self.assertAlmostEqual(loro["mean_rps"], 0.1, places=12)
        self.assertAlmostEqual(loro["mean_tvd"], 0.5, places=12)
        self.assertAlmostEqual(loro["empirical_disagreement_floor_rps"], 0.025, places=12)
        self.assertAlmostEqual(loro["unbiased_finite_sample_noise_term_s2_over_m"], 0.025, places=12)

    def test_loro_rejects_single_rater(self) -> None:
        with self.assertRaisesRegex(ValueError, "at least two ratings"):
            mod._compute_loro_ceiling({"i1": {}}, {"i1": [("R1", 5)]})

    def test_corr_ci_perm_edge_cases(self) -> None:
        too_short = mod._corr_ci_perm([1.0, 2.0], [2.0, 4.0], "pearson", draws=50, seed=1)
        self.assertEqual(too_short["n"], 2)
        self.assertAlmostEqual(too_short["value"], 1.0, places=12)
        self.assertIsNone(too_short["ci95"])
        self.assertIsNone(too_short["perm_p_one_sided"])

        const_res = mod._corr_ci_perm([2.0, 2.0, 2.0, 2.0], [1.0, 2.0, 3.0, 4.0], "spearman", draws=50, seed=1)
        self.assertEqual(const_res["n"], 4)
        self.assertIsNone(const_res["value"])
        self.assertIsNone(const_res["ci95"])
        self.assertIsNone(const_res["perm_p_one_sided"])

    def test_exp39_requires_at_least_90_percent_item_coverage(self) -> None:
        items = [f"item{i}" for i in range(45)]
        dataset = {iid: {"ratings": [5]} for iid in items}
        unit = {"criteria": {"heldout": {"spearman": None}}}
        for n_scored in (40, 41):
            harvest = {"cells": [
                {"kind": "crit", "status": "measured", "score": 1.0, "item": iid}
                for iid in items[:n_scored]
            ]}
            path = mock.Mock()
            path.read_text.return_value = json.dumps(harvest)
            score = mod._score_e39_unit(path, unit, items, dataset)
            if n_scored == 40:
                self.assertIsNone(score)  # 40/45 is only 88.9%.
            else:
                self.assertEqual(score["n_items"], 41)


if __name__ == "__main__":
    unittest.main()
