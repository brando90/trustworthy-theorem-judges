"""Experiment 14 (copy of experiment 12's run_exp12.py; only change: NNLS Pearson solver for large pools).
Experiment 12: formulation 2 (judge picked by correlation with the human ratings on train tasks) versus formulation 4
(judge picked by cross-entropy on train tasks), many task-grouped 20/5 splits plus one fixed split, cached judges, CPU only, zero model calls.
Usage: ~/.venvs/judge/bin/python run_pool.py --data dataset.json --out results [--splits 1000 --boot 10000]"""
import argparse, json, time, platform
from pathlib import Path
import numpy as np, scipy
from scipy.stats import rankdata
from common import *
from ce_mixture import fit
from nnls_pearson import fit_pearson  # exact Pearson-maximizing mixture for any pool size (experiment 3's enumeration is capped at 8 judges)

ap = argparse.ArgumentParser(); ap.add_argument('--data', required=True); ap.add_argument('--out', required=True)
ap.add_argument('--splits', type=int, default=1000); ap.add_argument('--boot', type=int, default=10000); ap.add_argument('--spearman_draws', type=int, default=4000)
a = ap.parse_args(); t0 = time.time()
d, rows, order, p, q, tasks = load(a.data); N, J = len(rows), len(order); ut = sorted(set(tasks)); T = len(ut)
tidx = np.array([ut.index(t) for t in tasks])
mu_q = q @ GRID                                               # N x J expected rating of each judge
METH = ['constant', 'equal_mixture', 'corr_single', 'corr_mixture_pearson', 'corr_mixture_spearman', 'ce_single', 'ce_mixture']
LABEL = {'constant': 'constant (train marginal)', 'equal_mixture': 'equal-weight mixture', 'corr_single': '② best single judge by train Pearson',
         'corr_mixture_pearson': '② mixture maximizing train Pearson', 'corr_mixture_spearman': '② mixture maximizing train Spearman',
         'ce_single': '④ best single judge by train CE', 'ce_mixture': '④ mixture minimizing train CE'}

def fit_all(tr, rng):
    """Every method is fitted from training artifacts only; returns {method: output distributions function of artifact index set} as weights."""
    pt, qt = p[tr], q[tr]; hm = pt @ GRID; W = {}; info = {}
    marg = smooth(pt.mean(0), EPS)
    W['constant'] = None; W['equal_mixture'] = np.full(J, 1/J)
    pe = np.array([pearson(mu_q[tr, j], hm) for j in range(J)]); pe = np.nan_to_num(pe, nan=-2)
    b = int(np.argmax(pe)); W['corr_single'] = np.eye(J)[b]; info['corr_single'] = b
    w, rec = fit_pearson(qt, pt); W['corr_mixture_pearson'] = w; info['corr_mixture_pearson_status'] = rec['status']
    # Spearman: vertices + equal + random simplex points, best train Spearman (finite search; no closed-form solver)
    cand = np.vstack([np.eye(J), np.full((1, J), 1/J), rng.dirichlet(np.ones(J), size=a.spearman_draws)])
    mu = mu_q[tr] @ cand.T; rk = rankdata(mu, axis=0); rt = rankdata(hm)
    rk -= rk.mean(0); rtc = rt - rt.mean(); den = np.linalg.norm(rk, axis=0)*np.linalg.norm(rtc)
    sp = np.where(den > 1e-12, (rk*rtc[:, None]).sum(0)/np.where(den > 1e-12, den, 1), -2)
    W['corr_mixture_spearman'] = cand[int(np.argmax(sp))]
    ce_s = [ce(pt, qt[:, j]).mean() for j in range(J)]; b = int(np.argmin(ce_s)); W['ce_single'] = np.eye(J)[b]; info['ce_single'] = b
    w, rec = fit(qt, pt, 'ce'); W['ce_mixture'] = w; info['ce_mixture_status'] = rec['status']
    return W, marg, info

def predict(W, marg, te):
    return {m: (np.tile(marg, (len(te), 1)) if W[m] is None else np.einsum('njr,j->nr', q[te], W[m])) for m in METH}

SUM = {mt: {m: np.zeros(N) for m in METH} for mt in ['ce', 'rps', 'tvd']}; CNT = np.zeros(N)
CSUM = {mt: {m: np.zeros(T) for m in METH} for mt in ['pearson', 'spearman']}; CCNT = {mt: {m: np.zeros(T) for m in METH} for mt in ['pearson', 'spearman']}
CSPLIT = {mt: {m: [] for m in METH} for mt in ['pearson', 'spearman']}
wts = {m: [] for m in METH}; fails = 0; picks = {'corr_single': np.zeros(J, int), 'ce_single': np.zeros(J, int)}
for s in range(a.splits):
    tr, te = split_tasks(tasks, REPEAT_SEED0 + s); rng = np.random.default_rng(REPEAT_SEED0 + s)
    W, marg, info = fit_all(tr, rng); Q = predict(W, marg, te)
    fails += int(info['corr_mixture_pearson_status'] not in ('optimal_cone_projection',) ) + int(info['ce_mixture_status'] != 'optimal')
    picks['corr_single'][info['corr_single']] += 1; picks['ce_single'][info['ce_single']] += 1
    CNT[te] += 1; tt = np.unique(tidx[te])
    for m in METH:
        sc = score(p[te], Q[m]); wts[m].append(None if W[m] is None else W[m].tolist())
        for mt in SUM: SUM[mt][m][te] += sc[mt]
        for mt in CSUM:
            CSPLIT[mt][m].append(sc[mt])
            if np.isfinite(sc[mt]): CSUM[mt][m][tt] += sc[mt]; CCNT[mt][m][tt] += 1
assert (CNT > 0).all(), 'every artifact must be tested at least once'
per = {mt: {m: SUM[mt][m]/CNT for m in METH} for mt in SUM}                # per-artifact mean over the splits where it was a test artifact
tsum = lambda x: (np.bincount(tidx, weights=x, minlength=T), np.bincount(tidx, minlength=T))
rng = np.random.default_rng(1210); draws = rng.integers(0, T, size=(a.boot, T))
res = {'n_artifacts': N, 'n_tasks': T, 'splits': a.splits, 'train_tasks': 20, 'test_tasks': 5, 'bootstrap_draws': a.boot, 'epsilon': EPS, 'candidate_order': order,
       'spearman_search_draws': a.spearman_draws, 'optimizer_certificate_failures': fails, 'inference_calls': 0, 'provider_cost_usd': 0,
       'test_count_per_artifact_min_max': [int(CNT.min()), int(CNT.max())], 'metrics': {}, 'corr_metrics': {}, 'paired': {}, 'mean_weights': {}, 'single_judge_choice_counts': {k: dict(zip(order, v.tolist())) for k, v in picks.items()}}
def boot_paired(diff_t, n_t):
    point = float(diff_t.sum()/n_t.sum()); bs = np.array([diff_t[dr].sum()/n_t[dr].sum() for dr in draws]); lo, hi = np.percentile(bs, [2.5, 97.5])
    return {'point': point, 'ci95': [float(lo), float(hi)], 'excludes_zero': bool(lo > 0 or hi < 0)}
PAIRS = [('corr_mixture_pearson', 'ce_mixture'), ('corr_mixture_spearman', 'ce_mixture'), ('corr_single', 'ce_single')]
for mt in SUM:
    res['metrics'][mt] = {m: float(per[mt][m].mean()) for m in METH}
    for x, y in PAIRS + [('ce_mixture', 'constant'), ('ce_mixture', 'equal_mixture'), ('corr_mixture_pearson', 'constant'), ('corr_mixture_pearson', 'equal_mixture')]:
        st, n_t = tsum(per[mt][x]-per[mt][y]); r = boot_paired(st, n_t); r['tasks_first_better'] = int((st < 0).sum()); res['paired'][f'{mt}: {x} minus {y}'] = r
# correlations: split-level value attributed to its 5 test tasks, averaged per task, then task bootstrap
for mt in CSUM:
    tm = {m: np.where(CCNT[mt][m] > 0, CSUM[mt][m]/np.maximum(CCNT[mt][m], 1), np.nan) for m in METH}
    res['corr_metrics'][mt] = {m: {'mean_over_splits': float(np.nanmean(CSPLIT[mt][m])) if np.isfinite(CSPLIT[mt][m]).any() else None,
                                   'split_p05_p95': [float(v) for v in np.nanpercentile(CSPLIT[mt][m], [5, 95])] if np.isfinite(CSPLIT[mt][m]).any() else None,
                                   'undefined_splits': int(np.isnan(CSPLIT[mt][m]).sum())} for m in METH}
    for x, y in PAIRS:
        ok = np.isfinite(tm[x]) & np.isfinite(tm[y]); dt = np.where(ok, tm[x]-tm[y], 0.0); n = ok.astype(float)
        bs = np.array([dt[dr].sum()/max(n[dr].sum(), 1) for dr in draws]); lo, hi = np.percentile(bs, [2.5, 97.5])
        res['paired'][f'{mt} (test-set correlation, task-attributed): {x} minus {y}'] = {'point': float(dt.sum()/n.sum()), 'ci95': [float(lo), float(hi)], 'excludes_zero': bool(lo > 0 or hi < 0)}
for m in METH:
    if wts[m][0] is not None: res['mean_weights'][m] = np.mean(wts[m], 0).tolist()
# fixed split (seed FIXED_SEED, declared in common.py before fitting)
tr, te = split_tasks(tasks, FIXED_SEED); W, marg, info = fit_all(tr, np.random.default_rng(FIXED_SEED)); Q = predict(W, marg, te)
fx = {'test_tasks': sorted(set(tasks[te])), 'train_n': len(tr), 'test_n': len(te), 'weights': {m: (None if W[m] is None else W[m].tolist()) for m in METH}, 'test': {}}
for m in METH:
    sc = score(p[te], Q[m]); fx['test'][m] = {k: (float(v.mean()) if hasattr(v, 'mean') else v) for k, v in sc.items()}
    fx['test'][m]['per_task'] = {t: {k: float(sc[k][tasks[te] == t].mean()) for k in ['ce', 'rps', 'tvd']} for t in sorted(set(tasks[te]))}
res['fixed_split'] = fx; res['seconds'] = time.time()-t0
res['environment'] = {'python': platform.python_version(), 'numpy': np.__version__, 'scipy': scipy.__version__}
out = Path(a.out); out.mkdir(parents=True, exist_ok=True); json.dump(res, open(out/'results.json', 'w'), indent=1)
json.dump({'per_artifact': {mt: {m: per[mt][m].tolist() for m in METH} for mt in per}, 'labels': LABEL}, open(out/'per_artifact.json', 'w'))
print(json.dumps({k: res[k] for k in ['metrics', 'paired', 'corr_metrics', 'mean_weights', 'single_judge_choice_counts', 'optimizer_certificate_failures', 'seconds']}, indent=1))
