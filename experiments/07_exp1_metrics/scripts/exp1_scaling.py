#!/usr/bin/env python3
"""TLDR: Subsampling fit of l = E + A n^-alpha + B k^-beta (and MSE(n,k,m) = E0 + A/n^a + B/k + C/m^b) on the cached judge scores and human ratings (no model calls).

Reading used (see README): the cached judges are not trained on tasks, so l is the squared ESTIMATION error of a judge's nRMSE (scores/5),
measured on n tasks with k human ratings per item and m judge repeats, against the value on the 13 disjoint held-out tasks with all human ratings and m=3.
n = tasks, k = human ratings per item (D = 3n k ratings per judge-evaluation in total), m = sampled judge repeats. Human panel: all five rater columns
(every item has >=4 ratings, so k=1..4; the 3-expert panel has only 2 ratings on 30 items). Extrapolation beyond n=12, k=4, m=3 is labelled as such.
"""
import argparse, json
import numpy as np
from scipy.optimize import least_squares

SEED = 20261109
NS = [2, 3, 4, 6, 8, 10, 12]
KS = [1, 2, 3, 4]
MS = [1, 2, 3]


def load(private):
    ds = json.load(open(f'{private}/dataset.json'))
    path = f'{private}/source/experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test/inputs/items.jsonl'
    byitem = {}
    for l in open(path):
        if l.strip():
            r = json.loads(l); byitem[r['item']] = r
    H = np.full((75, 5), np.nan)
    for i, r in enumerate(ds['rows']):
        for c, k in enumerate(['p1', 'p2', 'p3', 'p4', 'p5']):
            v = byitem[r['item']][k]
            if v is not None: H[i, c] = v
    names = list(ds['outputs'])
    J = np.stack([np.array(ds['outputs'][n], float) for n in names])  # (judge, item, 3)
    tasks = np.array([r['task'] for r in ds['rows']])
    return names, J, H, tasks


def simulate(J, H, task_idx, tasks_u, rng, draws, task_subset=None):
    """Returns l[n,k,m] pooled over judges and per judge (judge, n,k,m): mean over draws of (nRMSE_hat - nRMSE_ref)^2, plus the mean of nRMSE_hat and ref."""
    ntask = len(tasks_u) if task_subset is None else len(task_subset)
    pool = np.arange(len(tasks_u)) if task_subset is None else np.array(task_subset)
    items_by_task = [np.where(task_idx == t)[0] for t in pool]
    assert all(len(x) == 3 for x in items_by_task)
    nref = ntask - max(NS)
    nj = J.shape[0]
    sq = np.zeros((nj, len(NS), len(KS), len(MS)))
    hat_sum = np.zeros_like(sq)
    ref_sum = 0.0
    for _ in range(draws):
        perm = rng.permutation(ntask)
        order = np.concatenate([items_by_task[t] for t in perm])  # item order by task permutation
        # human k-rater means in random priority per item
        Hs = H[order]
        pr = rng.random(Hs.shape); pr[np.isnan(Hs)] = np.inf
        srt = np.argsort(pr, 1)
        Hp = np.take_along_axis(Hs, srt, 1)
        cnt = (~np.isnan(Hp)).sum(1)
        hk = np.stack([np.nanmean(Hp[:, :k], 1) for k in KS]) / 5.0  # (k, item)
        hfull = np.nanmean(Hs, 1) / 5.0
        # judge m-repeat means in random priority per item
        Js = J[:, order, :]
        prj = rng.random(Js.shape[1:])
        sj = np.argsort(prj, 1)
        Jp = np.take_along_axis(Js, sj[None], 2)
        jm = np.stack([Jp[:, :, :m].mean(2) for m in MS], 1) / 5.0  # (judge, m, item)
        # squared errors (judge, m, k, item)
        e = (jm[:, :, None, :] - hk[None, None, :, :]) ** 2
        cs = np.cumsum(e, axis=3)
        ref_items = slice(3 * max(NS), 3 * ntask)
        ref = np.sqrt(((jm[:, 2, :] - hfull[None, :]) ** 2)[:, ref_items].mean(1))  # (judge)
        for a, n in enumerate(NS):
            hat = np.sqrt(cs[:, :, :, 3 * n - 1] / (3 * n))  # (judge, m, k)
            hat = np.transpose(hat, (0, 2, 1))  # (judge, k, m)
            sq[:, a] += (hat - ref[:, None, None]) ** 2
            hat_sum[:, a] += hat
        ref_sum += ref
    return sq / draws, hat_sum / draws, ref_sum / draws


def f_n_k(p, n, k):
    E, A, al, B_, be = p
    return E + A * n ** (-al) + B_ * k ** (-be)


def f_nkm(p, n, k, m):
    E0, A, a, B_, C, b = p
    return E0 + A / n ** a + B_ / k + C / m ** b


def f_nkm_free(p, n, k, m):
    E0, A, a, B_, bk, C, b = p
    return E0 + A / n ** a + B_ / k ** bk + C / m ** b


def fit(fun, lo, hi, starts, data, args_list):
    best = None
    lv = np.log(data)
    for s in starts:
        try:
            r = least_squares(lambda p: np.log(np.maximum(fun(p, *args_list), 1e-12)) - lv, s, bounds=(lo, hi), max_nfev=4000)
        except Exception:
            continue
        if best is None or r.cost < best.cost: best = r
    return best


def fit_all(L):
    """L: (n,k,m) mean estimation error. Fits F1 on m=3, F2 on all m, F2b free k exponent."""
    N, K, M = np.meshgrid(NS, KS, MS, indexing='ij')
    out = {}
    d1 = L[:, :, 2]; n1, k1 = np.meshgrid(NS, KS, indexing='ij')
    lo = [0, 0, 0.05, 0, 0.05]; hi = [1, 10, 4, 10, 4]
    starts = [[e, a, al, b, be] for e in (1e-4, 1e-3) for a in (0.01, 0.1) for al in (0.5, 1, 2) for b in (1e-3, 1e-2) for be in (0.5, 1, 2)]
    r = fit(f_n_k, lo, hi, starts, d1.ravel(), (n1.ravel(), k1.ravel()))
    out['F1'] = dict(params=dict(zip(['E', 'A', 'alpha', 'B', 'beta'], map(float, r.x))), fit_rmse_log=float(np.sqrt(2 * r.cost / d1.size)),
                     pred=f_n_k(r.x, n1, k1).tolist(), obs=d1.tolist())
    lo2 = [0, 0, 0.05, 0, 0, 0.05]; hi2 = [1, 10, 4, 10, 10, 4]
    starts2 = [[e, a, al, b, c, bb] for e in (1e-4, 1e-3) for a in (0.01, 0.1) for al in (0.5, 1, 2) for b in (1e-3, 1e-2) for c in (1e-3, 1e-2) for bb in (0.5, 1, 2)]
    r2 = fit(f_nkm, lo2, hi2, starts2, L.ravel(), (N.ravel(), K.ravel(), M.ravel()))
    out['F2'] = dict(params=dict(zip(['E0', 'A', 'a', 'B', 'C', 'b'], map(float, r2.x))), fit_rmse_log=float(np.sqrt(2 * r2.cost / L.size)))
    lo3 = [0, 0, 0.05, 0, 0.05, 0, 0.05]; hi3 = [1, 10, 4, 10, 4, 10, 4]
    starts3 = [[e, a, al, b, bk, c, bb] for e in (1e-4, 1e-3) for a in (0.01, 0.1) for al in (0.5, 1) for b in (1e-3, 1e-2) for bk in (1, 2) for c in (1e-3, 1e-2) for bb in (1,)]
    r3 = fit(f_nkm_free, lo3, hi3, starts3, L.ravel(), (N.ravel(), K.ravel(), M.ravel()))
    out['F2_free_k'] = dict(params=dict(zip(['E0', 'A', 'a', 'B', 'beta_k', 'C', 'b'], map(float, r3.x))), fit_rmse_log=float(np.sqrt(2 * r3.cost / L.size)))
    return out


def requirement(params, target, form='F1'):
    """Smallest (n,k) on a grid with predicted sqrt(reducible l) <= target (reducible = l - E), and with E included. m=3."""
    res = {}
    for label, inc in (('reducible_only', False), ('including_floor_E', True)):
        found = None
        for n in list(range(2, 201)):
            for k in range(1, 41):
                l = f_n_k([params['E'], params['A'], params['alpha'], params['B'], params['beta']], n, k)
                if not inc: l = l - params['E']
                if np.sqrt(l) <= target:
                    cand = (n, k, n * k * 3)
                    if found is None or cand[2] < found[2]: found = cand
        res[label] = dict(n=found[0], k=found[1], total_ratings=found[2]) if found else None
    return res


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--private', required=True); ap.add_argument('--out', required=True)
    ap.add_argument('--draws', type=int, default=20000); ap.add_argument('--refit-boot', type=int, default=500)
    a = ap.parse_args()
    names, J, H, tasks = load(a.private)
    tasks_u, task_idx = np.unique(tasks, return_inverse=True)
    rng = np.random.default_rng(SEED)
    sq, hat, ref = simulate(J, H, task_idx, tasks_u, rng, a.draws)
    pooled = sq.mean(0)
    res = dict(grid=dict(n=NS, k=KS, m=MS), draws=a.draws, seed=SEED, ref_nrmse_mean_over_draws={n: float(ref[i]) for i, n in enumerate(names)},
               pooled_l=pooled.tolist(), per_judge_l={n: sq[i].tolist() for i, n in enumerate(names)})
    res['fit_pooled'] = fit_all(pooled)
    res['fit_per_judge_F1'] = {}
    for i, n in enumerate(names):
        r = fit_all(sq[i]); res['fit_per_judge_F1'][n] = dict(F1=r['F1']['params'], F1_fit_rmse_log=r['F1']['fit_rmse_log'], F2=r['F2']['params'], F2_fit_rmse_log=r['F2']['fit_rmse_log'])
    # Monte-Carlo CIs: split draws into independent batches, refit each (batches resampled with replacement)
    nb = 40; per = a.draws // nb
    batches = []
    for b in range(nb):
        s, _, _ = simulate(J, H, task_idx, tasks_u, np.random.default_rng(SEED + 1 + b), per)
        batches.append(s.mean(0))
    batches = np.array(batches)
    brng = np.random.default_rng(SEED + 999)
    bf1, bf2, bfk = [], [], []
    for _ in range(a.refit_boot):
        pick = brng.integers(0, nb, nb)
        f = fit_all(batches[pick].mean(0))
        bf1.append([f['F1']['params'][k] for k in ['E', 'A', 'alpha', 'B', 'beta']])
        bf2.append([f['F2']['params'][k] for k in ['E0', 'A', 'a', 'B', 'C', 'b']])
    bf1 = np.array(bf1); bf2 = np.array(bf2)
    ci = lambda arr, keys: {k: [float(np.percentile(arr[:, i], 2.5)), float(np.percentile(arr[:, i], 97.5))] for i, k in enumerate(keys)}
    res['ci_mc_F1'] = ci(bf1, ['E', 'A', 'alpha', 'B', 'beta']); res['ci_mc_F2'] = ci(bf2, ['E0', 'A', 'a', 'B', 'C', 'b'])
    # task-set sensitivity: leave 5 tasks out (5 folds of 5 tasks), n<=12 needs ntask>=13+; 20 tasks leaves 8 held out
    folds = np.array_split(np.random.default_rng(SEED + 7).permutation(25), 5)
    loo = []
    for f in folds:
        keep = [t for t in range(25) if t not in set(f)]
        s, _, _ = simulate(J, H, task_idx, tasks_u, np.random.default_rng(SEED + 50), a.draws // 4, task_subset=keep)
        loo.append(fit_all(s.mean(0))['F1']['params'])
    res['task_sensitivity_F1_leave5tasks_out'] = loo
    p = res['fit_pooled']['F1']['params']
    res['requirement_F1'] = {str(t): requirement(p, t) for t in (0.02, 0.01)}
    json.dump(res, open(a.out, 'w'), indent=1)
    print(json.dumps({k: res['fit_pooled'][k]['params'] for k in res['fit_pooled']}, indent=1))


if __name__ == '__main__':
    main()
