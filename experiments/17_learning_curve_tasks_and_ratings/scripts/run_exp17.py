"""Experiment 17: learning curve of a learned judge on the real human ratings. Held-out RPS against the number of training tasks (4 to 20, nested)
and against the number of human ratings per artifact used for training (1, 2, all), for the CE mixture (④), the Pearson mixture (②) and baselines.
Cached judges (experiment 12 dataset), CPU only, zero model calls. Test tasks per split are the same 5 as experiment 12 (seeds 20261210+s).
Usage: ~/.venvs/judge/bin/python run_exp17.py --data dataset.json --out results [--splits 1000 --boot 10000]
Imports the shared code (common.py, exp10_scripts, vendor_exp03) from ../../16_formulation3_val_selection_vs_4/scripts."""
import argparse, json, sys, time, platform
from pathlib import Path
from multiprocessing import Pool
import numpy as np, scipy
from scipy.optimize import curve_fit
sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'16_formulation3_val_selection_vs_4'/'scripts'))
from common import *
from ce_mixture import fit

ap = argparse.ArgumentParser(); ap.add_argument('--data', required=True); ap.add_argument('--out', required=True)
ap.add_argument('--splits', type=int, default=1000); ap.add_argument('--boot', type=int, default=10000); ap.add_argument('--fitboot', type=int, default=2000)
a = ap.parse_args(); t0 = time.time()
d, rows, order, p, q, tasks = load(a.data); N, J = len(rows), len(order); ut = sorted(set(tasks)); T = len(ut)
tidx = np.array([ut.index(t) for t in tasks]); mu_q = q @ GRID
NS = [4, 6, 8, 10, 12, 14, 16, 18, 20]; KS = [1, 2, 3]
METH = ['constant', 'equal_mixture', 'corr_single', 'corr_mixture_pearson', 'ce_single', 'ce_mixture']
LABEL = {'constant': 'constant (train marginal)', 'equal_mixture': 'equal-weight mixture', 'corr_single': '② best single judge by train Pearson',
         'corr_mixture_pearson': '② mixture maximizing train Pearson', 'ce_single': '④ best single judge by train CE', 'ce_mixture': '④ mixture minimizing train CE'}
ratings = [np.array(r['ratings']) for r in rows]

def fit_predict(idx, ptrain, te):
    """Fit every method from artifacts idx with training label histograms ptrain (rows aligned with idx); return {method: Q on te}."""
    qt = q[idx]; hm = ptrain @ GRID; Q = {}
    Q['constant'] = np.tile(smooth(ptrain.mean(0), EPS), (len(te), 1)); Q['equal_mixture'] = q[te].mean(1)
    pe = np.nan_to_num([pearson(mu_q[idx, j], hm) for j in range(J)], nan=-2); Q['corr_single'] = q[te][:, int(np.argmax(pe))]
    w, _ = fit(qt, ptrain, 'pearson'); Q['corr_mixture_pearson'] = np.einsum('njr,j->nr', q[te], w)
    Q['ce_single'] = q[te][:, int(np.argmin([ce(ptrain, qt[:, j]).mean() for j in range(J)]))]
    w, _ = fit(qt, ptrain, 'ce'); Q['ce_mixture'] = np.einsum('njr,j->nr', q[te], w)
    return Q

def run_split(s):
    tr, te = split_tasks(tasks, REPEAT_SEED0 + s); rng = np.random.default_rng(555000 + s)
    trt = sorted(set(tasks[tr])); perm = rng.permutation(trt).tolist(); res = {}
    for n in NS:                                                       # nested subsets of the 20 train tasks: first n of one permutation
        keep = set(perm[:n]); idx = tr[np.array([t in keep for t in tasks[tr]])]
        Q = fit_predict(idx, p[idx], te); res[('n', n)] = {m: score(p[te], Q[m]) for m in METH}
    for k in KS:                                                       # all 20 train tasks, k randomly chosen ratings per artifact
        pk = np.array([histogram(rng.permutation(ratings[i])[:k]) if len(ratings[i]) >= k else p[i] for i in tr])
        Q = fit_predict(tr, pk, te); res[('k', k)] = {m: score(p[te], Q[m]) for m in METH}
    return te, res

def powerlaw(n, E, A, al): return E + A*n**(-al)
def fit_pl(x, y):
    try:
        po, _ = curve_fit(powerlaw, x, y, p0=[y.min()*0.9, max(y.max()-y.min(), 1e-3)*4**0.5, 0.5], bounds=([0, 0, 0.01], [1, 5, 3]), maxfev=5000)
        return po
    except Exception: return None

if __name__ == '__main__':
    with Pool(4) as pool: R = pool.map(run_split, range(a.splits), chunksize=10)
    keys = [('n', n) for n in NS] + [('k', k) for k in KS]; MT = ['rps', 'ce', 'tvd']
    SUM = {kk: {mt: {m: np.zeros(N) for m in METH} for mt in MT} for kk in keys}; CNT = np.zeros(N)
    for te, res in R:
        CNT[te] += 1
        for kk in keys:
            for m in METH:
                for mt in MT: SUM[kk][mt][m][te] += res[kk][m][mt]
    assert (CNT > 0).all()
    per = {kk: {mt: {m: SUM[kk][mt][m]/CNT for m in METH} for mt in MT} for kk in keys}
    rng = np.random.default_rng(1210); draws = rng.integers(0, T, size=(a.boot, T))
    nt = np.bincount(tidx, minlength=T).astype(float)
    def tmean(x): return np.bincount(tidx, weights=x, minlength=T)                       # per-task sum of per-artifact values
    def ci(x_t, n_t=nt, dr=draws):
        point = float(x_t.sum()/n_t.sum()); bs = np.array([x_t[r].sum()/n_t[r].sum() for r in dr]); lo, hi = np.percentile(bs, [2.5, 97.5])
        return {'point': point, 'ci95': [float(lo), float(hi)]}
    out = {'n_artifacts': N, 'n_tasks': T, 'splits': a.splits, 'NS': NS, 'KS': KS, 'bootstrap_draws': a.boot, 'epsilon': EPS, 'candidate_order': order, 'labels': LABEL,
           'inference_calls': 0, 'provider_cost_usd': 0, 'curve_tasks': {}, 'curve_ratings': {}, 'paired_ce_minus_corr': {}, 'drop_4_to_20': {}, 'powerlaw': {}}
    for mt in MT:
        out['curve_tasks'][mt] = {m: {str(n): ci(tmean(per[('n', n)][mt][m])) for n in NS} for m in METH}
        out['curve_ratings'][mt] = {m: {str(k): ci(tmean(per[('k', k)][mt][m])) for k in KS} for m in METH}
    for n in NS:
        out['paired_ce_minus_corr'][str(n)] = ci(tmean(per[('n', n)]['rps']['ce_mixture']-per[('n', n)]['rps']['corr_mixture_pearson']))
    for m in METH:
        out['drop_4_to_20'][m] = ci(tmean(per[('n', 4)]['rps'][m]-per[('n', 20)]['rps'][m]))          # positive = more tasks lower RPS
    for k in KS[:-1]:
        out['drop_4_to_20'][f'ce_mixture, ratings {k} to all'] = ci(tmean(per[('k', k)]['rps']['ce_mixture']-per[('k', 3)]['rps']['ce_mixture']))
    # power law RPS(n) = E + A n^-alpha for the two mixtures, task bootstrap of the whole curve
    for m in ['ce_mixture', 'corr_mixture_pearson', 'equal_mixture']:
        pts = np.array([tmean(per[('n', n)]['rps'][m]) for n in NS])                      # len(NS) x T per-task sums
        y = pts.sum(1)/nt.sum(); po = fit_pl(np.array(NS, float), y); brng = np.random.default_rng(99); fits = []; failed = 0
        for _ in range(a.fitboot):
            r = brng.integers(0, T, size=T); yb = pts[:, r].sum(1)/nt[r].sum(); pb = fit_pl(np.array(NS, float), yb)
            if pb is None: failed += 1
            else: fits.append(pb)
        fits = np.array(fits)
        out['powerlaw'][m] = {'point_E_A_alpha': None if po is None else po.tolist(), 'bootstrap_alpha_p2.5_p50_p97.5': np.percentile(fits[:, 2], [2.5, 50, 97.5]).tolist() if len(fits) else None,
                              'bootstrap_E_p2.5_p50_p97.5': np.percentile(fits[:, 0], [2.5, 50, 97.5]).tolist() if len(fits) else None,
                              'bootstrap_fraction_alpha_at_bound': float(np.mean((fits[:, 2] > 2.99) | (fits[:, 2] < 0.011))) if len(fits) else None, 'failed_fits': failed, 'bootstrap_fits': int(len(fits))}
    out['seconds'] = time.time()-t0; out['environment'] = {'python': platform.python_version(), 'numpy': np.__version__, 'scipy': scipy.__version__}
    o = Path(a.out); o.mkdir(parents=True, exist_ok=True); json.dump(out, open(o/'results.json', 'w'), indent=1)
    for mt in ['rps']:
        print('tasks', NS)
        for m in METH: print(f'{m:22s}', ' '.join(f"{out['curve_tasks'][mt][m][str(n)]['point']:.4f}" for n in NS))
        for m in METH: print(f'ratings {m:22s}', ' '.join(f"{out['curve_ratings'][mt][m][str(k)]['point']:.4f}" for k in KS))
    print(json.dumps({k: out[k] for k in ['drop_4_to_20', 'paired_ce_minus_corr', 'powerlaw', 'seconds']}, indent=1))
