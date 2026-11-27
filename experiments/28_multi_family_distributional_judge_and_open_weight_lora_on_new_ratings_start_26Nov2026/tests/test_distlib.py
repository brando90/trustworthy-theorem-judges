import unittest
import sys
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import distlib as dl


class TestDistlib(unittest.TestCase):
    def test_analytic_gradients_match_finite_diff(self):
        rng = np.random.default_rng(42)
        n, m, d = 14, 3, 4
        raw_p = rng.dirichlet(np.ones(6), size=(n, m))
        lp_stack = np.array([dl.centered_log_probs(raw_p[:, j, :]) for j in range(m)]).transpose(1, 0, 2)
        z = rng.normal(size=(n, d))
        p_emp = rng.dirichlet(np.full(6, 0.7), size=n)

        for obj in ("ce", "rps", "pearson"):
            for use_quad in (True, False):
                cal = dl.MKCalibrator(objective=obj, alpha=0.35, alpha_a=0.05, use_quad=use_quad)
                dim = 6 + m + d * (2 if use_quad else 1)
                th = rng.normal(scale=0.3, size=dim)
                _, g_ana = cal.loss_and_grad(th, lp_stack, z, p_emp)
                eps = 1e-6
                g_num = np.zeros_like(th)
                for idx in range(dim):
                    t_p = th.copy(); t_p[idx] += eps
                    t_m = th.copy(); t_m[idx] -= eps
                    f_p, _ = cal.loss_and_grad(t_p, lp_stack, z, p_emp)
                    f_m, _ = cal.loss_and_grad(t_m, lp_stack, z, p_emp)
                    g_num[idx] = (f_p - f_m) / (2.0 * eps)
                max_err = float(np.max(np.abs(g_ana - g_num)))
                self.assertLess(max_err, 1e-7, f"Grad mismatch for {obj} quad={use_quad}: {max_err}")

    def test_icc_and_kendall_exactness(self):
        y = np.array([0.0, 1.0, 2.0, 3.0, 4.0, 5.0])
        # Perfect match -> ICC = 1, Kendall = 1
        a1, c1 = dl.icc_a1_and_c1(y, y)
        self.assertAlmostEqual(a1, 1.0, places=9)
        self.assertAlmostEqual(c1, 1.0, places=9)
        self.assertAlmostEqual(dl.kendall_tau_b(y, y), 1.0, places=9)
        # Constant shift +1 -> ICC(C,1)=1.0, ICC(A,1) < 1.0
        a1s, c1s = dl.icc_a1_and_c1(y + 1.0, y)
        self.assertAlmostEqual(c1s, 1.0, places=9)
        self.assertLess(a1s, 0.90)

    def test_proper_score_minimum(self):
        rng = np.random.default_rng(7)
        p = rng.dirichlet(np.ones(6), size=20)
        self.assertLessEqual(dl.rps_items(p, p).mean(), dl.rps_items(p, np.roll(p, 1, axis=1)).mean())
        self.assertLessEqual(dl.ce_items(p, p).mean(), dl.ce_items(p, np.roll(p, 1, axis=1)).mean())
        self.assertAlmostEqual(float(dl.tvd_items(p, p).mean()), 0.0, places=12)

    def test_load_bundle_hides_test_rows(self):
        import data_exp28 as de
        d_trva = de.load_bundle(include_test=False, require_complete=False)
        self.assertEqual(d_trva["n"], 105)
        self.assertNotIn("test", set(d_trva["exp27_split"]))
        # Incomplete artifacts dir must raise AssertionError under require_complete=True
        with self.assertRaises(AssertionError):
            de.load_bundle(include_test=False, h4_dir=Path("/tmp/nonexistent_dir_exp28"), require_complete=True)

    def test_nested_fold_disjointness(self):
        from search_inner_cv import make_4fold_inner_tasks
        import data_exp28 as de
        d_trva = de.load_bundle(include_test=False, require_complete=False)
        folds = make_4fold_inner_tasks(d_trva)
        for f in range(4):
            tr_tasks = set(d_trva["task"][folds != f])
            va_tasks = set(d_trva["task"][folds == f])
            self.assertEqual(len(tr_tasks & va_tasks), 0)

    def test_select_excludes_h3_and_frontier_excludes_qwen(self):
        import data_exp28 as de
        from final_eval_exp28 import select_best_on_subset
        d_trva = de.load_bundle(include_test=False, require_complete=True)
        best_s = select_best_on_subset(d_trva, set_aware_filter=True, exclude_h3=True, frontier_only=False)
        self.assertNotIn("h3_astra", best_s["dist_keys"])
        self.assertNotIn("h3_e", best_s["feat_keys"])
        self.assertNotIn("h3_s", best_s["feat_keys"])
        best_fg = select_best_on_subset(d_trva, set_aware_filter=False, exclude_h3=True, frontier_only=True)
        for qk in ("qwen3_8b", "qwen3_4b"):
            self.assertNotIn(qk, best_fg["dist_keys"])
        for fk in ("judge_std4", "e_q8b", "e_q4b", "is_new", "h3_e", "h3_s"):
            self.assertNotIn(fk, best_fg["feat_keys"])

    def test_bootstrap_tail_counts_and_mc_floor(self):
        rng = np.random.default_rng(123)
        tasks = np.array([f"t{i // 2}" for i in range(40)])
        p = rng.dirichlet(np.ones(6), size=40)
        q_bad = np.roll(p, 2, axis=1)
        out = dl.task_cluster_bootstrap(tasks, p, p, q_ref=q_bad, draws=200, seed=7)
        d = out["paired_vs_ref"]["dRPS"]
        self.assertEqual(d["n_draws"], 200)
        self.assertIn("n_ge_zero", d)
        self.assertIn("n_le_zero", d)
        self.assertAlmostEqual(d["p_val_mc_floor"], 2.0 / 201.0, places=12)

    def test_pearson_head_small_alpha_avoids_collapse(self):
        rng = np.random.default_rng(99)
        n = 60
        y_latent = rng.normal(size=n)
        p_raw = np.stack([np.exp(-0.5 * (dl.GRID - (2.5 + 1.1 * y_latent[i])) ** 2) for i in range(n)])
        p_raw /= p_raw.sum(axis=1, keepdims=True)
        p_emp = np.stack([np.exp(-0.5 * (dl.GRID - (2.6 + 1.0 * y_latent[i])) ** 2) for i in range(n)])
        p_emp /= p_emp.sum(axis=1, keepdims=True)
        lp = dl.centered_log_probs(p_raw)[:, None, :]
        x = (p_raw @ dl.GRID)[:, None]
        is_new = np.zeros(n)
        cal = dl.MKCalibrator(objective="pearson", alpha=1e-4, alpha_a=0.05, dirichlet_eta=0.0, use_quad=False, set_aware_prior=False)
        cal.fit(lp, x, is_new, p_emp)
        q = cal.predict(lp, x, is_new)
        e_pred = q @ dl.GRID
        self.assertGreater(float(np.std(e_pred)), 0.3)


if __name__ == "__main__":
    unittest.main()
