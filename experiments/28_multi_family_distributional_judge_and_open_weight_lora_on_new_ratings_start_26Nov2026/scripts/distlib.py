"""Experiment 28: (M+K) logit-space distributional calibration, metrics, and task-cluster bootstrap.

No sealed test access in search helpers; analytic gradients verified against finite differences (< 1e-8).
"""
from __future__ import annotations

import numpy as np
from scipy import optimize, stats

EPS = 1e-6
EPS_LOGPROB = 1e-4
GRID = np.arange(6, dtype=np.float64)
U_LIN = (GRID - 2.5) / 2.5
U_QUAD = U_LIN ** 2


def smooth(p: np.ndarray, eps: float = EPS) -> np.ndarray:
    p = np.maximum(np.asarray(p, dtype=np.float64), eps)
    return p / p.sum(axis=-1, keepdims=True)


def centered_log_probs(p: np.ndarray, eps: float = EPS_LOGPROB) -> np.ndarray:
    lp = np.log(smooth(p, eps=eps))
    return lp - lp.mean(axis=-1, keepdims=True)


def softmax(eta: np.ndarray) -> np.ndarray:
    e = np.exp(eta - eta.max(axis=-1, keepdims=True))
    return e / e.sum(axis=-1, keepdims=True)


def rps_items(p_emp: np.ndarray, q: np.ndarray) -> np.ndarray:
    cp = np.cumsum(p_emp, axis=-1)[..., :5]
    cq = np.cumsum(q, axis=-1)[..., :5]
    return np.mean((cq - cp) ** 2 + cp * (1.0 - cp), axis=-1)


def ce_items(p_emp: np.ndarray, q: np.ndarray) -> np.ndarray:
    qs = smooth(q, eps=EPS)
    return -np.sum(np.where(p_emp > 0, p_emp * np.log(qs), 0.0), axis=-1)


def tvd_items(p_emp: np.ndarray, q: np.ndarray) -> np.ndarray:
    return 0.5 * np.abs(q - p_emp).sum(axis=-1)


def brier_items(p_emp: np.ndarray, q: np.ndarray) -> np.ndarray:
    """Unbiased per-rating 6-class Brier score: E_Y ||q - e_Y||_2^2 averaged equally per artifact (range [0, 2])."""
    return np.sum((q - p_emp) ** 2, axis=-1) + (1.0 - np.sum(p_emp ** 2, axis=-1))


def mae_items(p_emp: np.ndarray, q: np.ndarray) -> np.ndarray:
    return np.abs((q @ GRID) - (p_emp @ GRID))


def _ranks_with_ties(x: np.ndarray) -> np.ndarray:
    n = len(x)
    order = np.argsort(x, kind="mergesort")
    ranks = np.empty(n, dtype=np.float64)
    i = 0
    while i < n:
        j = i + 1
        while j < n and x[order[j]] == x[order[i]]:
            j += 1
        r = 0.5 * (i + j - 1) + 1.0
        for k in range(i, j):
            ranks[order[k]] = r
        i = j
    return ranks


def pearson_r(a: np.ndarray, b: np.ndarray) -> float:
    a = np.asarray(a, dtype=np.float64)
    b = np.asarray(b, dtype=np.float64)
    if np.std(a) <= 1e-12 or np.std(b) <= 1e-12:
        return float("nan")
    return float(np.corrcoef(a, b)[0, 1])


def spearman_rho(a: np.ndarray, b: np.ndarray) -> float:
    return pearson_r(_ranks_with_ties(np.asarray(a)), _ranks_with_ties(np.asarray(b)))


def kendall_tau_b(a: np.ndarray, b: np.ndarray) -> float:
    a = np.asarray(a, dtype=np.float64)
    b = np.asarray(b, dtype=np.float64)
    if len(a) < 2 or np.std(a) <= 1e-12 or np.std(b) <= 1e-12:
        return float("nan")
    return float(stats.kendalltau(a, b, variant="b").statistic)


def icc_a1_and_c1(y_hat: np.ndarray, y: np.ndarray) -> tuple[float, float]:
    """Two-way mixed/random single-measure ICC(A,1) and ICC(C,1) for k=2 columns."""
    x = np.column_stack([np.asarray(y_hat, dtype=np.float64), np.asarray(y, dtype=np.float64)])
    n, k = x.shape
    if n < 2:
        return float("nan"), float("nan")
    grand = x.mean()
    rmean = x.mean(axis=1)
    cmean = x.mean(axis=0)
    msr = k * np.sum((rmean - grand) ** 2) / (n - 1)
    msc = n * np.sum((cmean - grand) ** 2) / (k - 1)
    resid = x - rmean[:, None] - cmean[None, :] + grand
    mse = np.sum(resid ** 2) / ((n - 1) * (k - 1))
    denom_c = msr + (k - 1) * mse
    denom_a = msr + (k - 1) * mse + (k / n) * (msc - mse)
    icc_c = float((msr - mse) / denom_c) if denom_c > 0 else float("nan")
    icc_a = float((msr - mse) / denom_a) if denom_a > 0 else float("nan")
    return icc_a, icc_c


def evaluate_panel(p_emp: np.ndarray, q: np.ndarray) -> dict[str, float]:
    eq = q @ GRID
    ep = p_emp @ GRID
    icc_a, icc_c = icc_a1_and_c1(eq, ep)
    return {
        "RPS": float(rps_items(p_emp, q).mean()),
        "CE": float(ce_items(p_emp, q).mean()),
        "TVD": float(tvd_items(p_emp, q).mean()),
        "Brier": float(brier_items(p_emp, q).mean()),
        "MAE": float(mae_items(p_emp, q).mean()),
        "Bias": float(eq.mean() - ep.mean()),
        "Mean_Judge": float(eq.mean()),
        "Mean_Human": float(ep.mean()),
        "ICC_A1": icc_a,
        "ICC_C1": icc_c,
        "Pearson": pearson_r(eq, ep),
        "Spearman": spearman_rho(eq, ep),
        "Kendall": kendall_tau_b(eq, ep),
    }


def task_cluster_bootstrap(
    tasks: np.ndarray,
    p_emp: np.ndarray,
    q: np.ndarray,
    q_ref: np.ndarray | None = None,
    draws: int = 10000,
    seed: int = 20261126,
) -> dict:
    """Task-cluster bootstrap matching Exp 27 exact resampling of unique task groups."""
    rng = np.random.default_rng(seed)
    ut = np.array(sorted(set(tasks)))
    groups = [np.where(tasks == t)[0] for t in ut]
    n_u = len(ut)

    rps_v = rps_items(p_emp, q)
    ce_v = ce_items(p_emp, q)
    tvd_v = tvd_items(p_emp, q)
    br_v = brier_items(p_emp, q)
    mae_v = mae_items(p_emp, q)
    eq = q @ GRID
    ep = p_emp @ GRID

    def _from_idx(idx: np.ndarray) -> dict[str, float]:
        icc_a, icc_c = icc_a1_and_c1(eq[idx], ep[idx])
        return {
            "RPS": float(rps_v[idx].mean()),
            "CE": float(ce_v[idx].mean()),
            "TVD": float(tvd_v[idx].mean()),
            "Brier": float(br_v[idx].mean()),
            "MAE": float(mae_v[idx].mean()),
            "Bias": float(eq[idx].mean() - ep[idx].mean()),
            "Mean_Judge": float(eq[idx].mean()),
            "Mean_Human": float(ep[idx].mean()),
            "ICC_A1": icc_a,
            "ICC_C1": icc_c,
            "Pearson": pearson_r(eq[idx], ep[idx]),
            "Spearman": spearman_rho(eq[idx], ep[idx]),
            "Kendall": kendall_tau_b(eq[idx], ep[idx]),
        }

    point = _from_idx(np.arange(len(tasks)))
    boot_vecs: dict[str, list[float]] = {k: [] for k in point}
    if q_ref is not None:
        rps_ref_v = rps_items(p_emp, q_ref)
        ce_ref_v = ce_items(p_emp, q_ref)
        tvd_ref_v = tvd_items(p_emp, q_ref)
        diff_vecs = {"dRPS": [], "dCE": [], "dTVD": []}
        diff_pt = {
            "dRPS": float(rps_v.mean() - rps_ref_v.mean()),
            "dCE": float(ce_v.mean() - ce_ref_v.mean()),
            "dTVD": float(tvd_v.mean() - tvd_ref_v.mean()),
        }

    for _ in range(draws):
        pick = rng.integers(0, n_u, n_u)
        idx = np.concatenate([groups[i] for i in pick])
        o = _from_idx(idx)
        for k, val in o.items():
            boot_vecs[k].append(val)
        if q_ref is not None:
            diff_vecs["dRPS"].append(float(rps_v[idx].mean() - rps_ref_v[idx].mean()))
            diff_vecs["dCE"].append(float(ce_v[idx].mean() - ce_ref_v[idx].mean()))
            diff_vecs["dTVD"].append(float(tvd_v[idx].mean() - tvd_ref_v[idx].mean()))

    ci = {
        k: [float(np.nanpercentile(v, 2.5)), float(np.nanpercentile(v, 97.5))]
        for k, v in boot_vecs.items()
    }
    res = {"point": point, "ci95": ci}
    if q_ref is not None:
        paired = {}
        for dk, arr_list in diff_vecs.items():
            arr = np.asarray(arr_list, dtype=np.float64)
            n_ge_zero = int(np.sum(arr >= 0.0))
            n_le_zero = int(np.sum(arr <= 0.0))
            p_pos = float(n_ge_zero / draws)
            p_neg = float(n_le_zero / draws)
            p_val = float(min(1.0, 2.0 * min(p_pos, p_neg)))
            paired[dk] = {
                "point": diff_pt[dk],
                "ci95": [float(np.percentile(arr, 2.5)), float(np.percentile(arr, 97.5))],
                "p_val_two_sided": p_val,
                "n_draws": int(draws),
                "n_ge_zero": n_ge_zero,
                "n_le_zero": n_le_zero,
                "p_val_mc_floor": float(2.0 / (draws + 1)),
            }
        res["paired_vs_ref"] = paired
    return res


class MKCalibrator:
    """(M + K) logit-pool distributional calibrator supporting CE, RPS, and Pearson objectives."""

    def __init__(
        self,
        objective: str = "ce",
        alpha: float = 1.0,
        alpha_a: float = 0.05,
        dirichlet_eta: float = 0.05,
        use_quad: bool = True,
        set_aware_prior: bool = True,
    ):
        assert objective in ("ce", "rps", "pearson")
        self.objective = objective
        self.alpha = float(alpha)
        self.alpha_a = float(alpha_a)
        self.dirichlet_eta = float(dirichlet_eta)
        self.use_quad = bool(use_quad)
        self.set_aware_prior = bool(set_aware_prior)

    def _unpack(self, theta: np.ndarray, m_dist: int, d_feat: int):
        a = theta[:6]
        off = 6
        tau = theta[off : off + m_dist]; off += m_dist
        w1 = theta[off : off + d_feat]; off += d_feat
        w2 = theta[off : off + d_feat] if self.use_quad else np.zeros(d_feat, dtype=np.float64)
        return a, tau, w1, w2

    def _eta(self, theta: np.ndarray, lp_stack: np.ndarray, z: np.ndarray) -> np.ndarray:
        # lp_stack: [N, M, 6], z: [N, D]
        a, tau, w1, w2 = self._unpack(theta, lp_stack.shape[1], z.shape[1])
        a0 = a - a.mean()
        eta = a0[None, :] + np.einsum("m,nmk->nk", tau, lp_stack)
        if z.shape[1] > 0:
            eta = eta + (z @ w1)[:, None] * U_LIN[None, :]
            if self.use_quad:
                eta = eta + (z @ w2)[:, None] * U_QUAD[None, :]
        return eta

    def loss_and_grad(self, theta: np.ndarray, lp_stack: np.ndarray, z: np.ndarray, p_emp: np.ndarray) -> tuple[float, np.ndarray]:
        n, m_dist, _ = lp_stack.shape
        d_feat = z.shape[1]
        a, tau, w1, w2 = self._unpack(theta, m_dist, d_feat)
        a0 = a - a.mean()
        eta = self._eta(theta, lp_stack, z)
        q = softmax(eta)

        if self.objective == "ce":
            lsm = eta - eta.max(axis=-1, keepdims=True) - np.log(np.exp(eta - eta.max(axis=-1, keepdims=True)).sum(axis=-1, keepdims=True))
            loss_data = float(-np.sum(p_emp * lsm) / n)
            d_eta = (q - p_emp) / n
        elif self.objective == "rps":
            cp = np.cumsum(p_emp, axis=-1)[:, :5]
            cq = np.cumsum(q, axis=-1)[:, :5]
            loss_data = float(np.mean((cq - cp) ** 2 + cp * (1.0 - cp)))
            # r_ij = 2/5 * (cq_ij - cp_ij) / n, g_ik = sum_{j=k}^4 r_ij
            r = (2.0 / 5.0) * (cq - cp) / n
            r_pad = np.pad(r, ((0, 0), (0, 1)), mode="constant")
            g = np.cumsum(r_pad[:, ::-1], axis=1)[:, ::-1]
            q_dot_g = np.sum(q * g, axis=1, keepdims=True)
            d_eta = q * (g - q_dot_g)
        else:  # pearson
            mu = q @ GRID
            y = p_emp @ GRID
            smu = float(np.std(mu))
            sy = float(np.std(y))
            if smu <= 1e-8 or sy <= 1e-8:
                loss_data = 0.0
                d_eta = np.zeros_like(q)
            else:
                ma = mu - mu.mean()
                yb = y - y.mean()
                n_a = float(np.linalg.norm(ma))
                n_b = float(np.linalg.norm(yb))
                r_val = float((ma @ yb) / (n_a * n_b))
                d_mu = -(yb / n_b - r_val * ma / n_a) / n_a
                loss_data = -r_val
                g = d_mu[:, None] * GRID[None, :]
                q_dot_g = np.sum(q * g, axis=1, keepdims=True)
                d_eta = q * (g - q_dot_g)

        reg = 0.5 * self.alpha_a * float(np.sum(a0 ** 2)) + 0.5 * self.alpha * float(np.sum(tau ** 2) + np.sum(w1 ** 2) + np.sum(w2 ** 2))
        da0 = d_eta.sum(axis=0) + self.alpha_a * a0
        da = da0 - da0.mean()
        dtau = np.einsum("nk,nmk->m", d_eta, lp_stack) + self.alpha * tau
        dw1 = z.T @ (d_eta @ U_LIN) + self.alpha * w1
        parts = [da, dtau, dw1]
        if self.use_quad:
            dw2 = z.T @ (d_eta @ U_QUAD) + self.alpha * w2
            parts.append(dw2)
        grad = np.concatenate(parts)
        return loss_data + reg, grad

    def fit(self, lp_stack: np.ndarray, x: np.ndarray, is_new: np.ndarray, p_emp: np.ndarray) -> "MKCalibrator":
        self.mu = x.mean(axis=0) if x.shape[1] > 0 else np.zeros(0)
        self.sd = (x.std(axis=0) + 1e-8) if x.shape[1] > 0 else np.zeros(0)
        z = (x - self.mu) / self.sd if x.shape[1] > 0 else np.zeros((len(p_emp), 0))
        m_dist = lp_stack.shape[1]
        d_feat = z.shape[1]

        # Empirical marginals (global and optional set-aware)
        self.p_global = smooth(p_emp.mean(axis=0), eps=EPS)
        self.p_by_set = {}
        for flag in (0.0, 1.0):
            mask = (is_new == flag)
            if mask.any():
                self.p_by_set[flag] = smooth(p_emp[mask].mean(axis=0), eps=EPS)
            else:
                self.p_by_set[flag] = self.p_global

        n_params = 6 + m_dist + d_feat * (2 if self.use_quad else 1)
        theta0 = np.zeros(n_params, dtype=np.float64)
        if self.objective == "pearson":
            # Break zero-variance saddle at theta=0 so Pearson has non-zero initial gradient
            if m_dist > 0:
                theta0[6 : 6 + m_dist] = 0.25 / m_dist
            elif d_feat > 0:
                theta0[6 + m_dist] = 0.5
        res = optimize.minimize(
            lambda th: self.loss_and_grad(th, lp_stack, z, p_emp),
            theta0,
            method="L-BFGS-B",
            jac=True,
        )
        self.theta = res.x
        return self

    def predict(self, lp_stack: np.ndarray, x: np.ndarray, is_new: np.ndarray) -> np.ndarray:
        z = (x - self.mu) / self.sd if x.shape[1] > 0 else np.zeros((len(lp_stack), 0))
        q_raw = softmax(self._eta(self.theta, lp_stack, z))
        if self.dirichlet_eta <= 0.0:
            return smooth(q_raw, eps=EPS)
        if self.set_aware_prior:
            prior = np.array([self.p_by_set[float(f)] for f in is_new])
        else:
            prior = np.broadcast_to(self.p_global[None, :], q_raw.shape)
        return smooth((1.0 - self.dirichlet_eta) * q_raw + self.dirichlet_eta * prior, eps=EPS)
