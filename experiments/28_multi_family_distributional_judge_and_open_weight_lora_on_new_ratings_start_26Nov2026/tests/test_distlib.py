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


if __name__ == "__main__":
    unittest.main()
