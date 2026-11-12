"""Experiment 16: formulation 3 (choose the judge by loss on a validation set, training data helps) versus formulation 4 (fit by loss on train tasks only)
and formulation 2 (fit by correlation on train tasks), many task-grouped splits, cached judges, CPU only, zero model calls.
Usage: ~/.venvs/judge/bin/python run_exp16.py --data dataset.json --out results [--splits 1000 --boot 10000]
Split rule: the same 20/5 train/test task splits as experiment 12 (seeds 20261210+s). Inside the 20 train tasks, 15 are the fit set and 5 the validation set (seed 777000+s)."""
import argparse, json, time, platform
from pathlib import Path
from multiprocessing import Pool
import numpy as np, scipy
from common import *
from ce_mixture import fit

SHRINK = [0.0, 0.25, 0.5, 0.75, 1.0]      # candidate family: CE-fitted mixture shrunk toward equal weights by lam (lam=1: equal mixture)
ap = argparse.ArgumentParser(); ap.add_argument('--data', required=True); ap.add_argument('--out', required=True)
ap.add_argument('--splits', type=int, default=1000); ap.add_argument('--boot', type=int, default=10000)
a = ap.parse_args(); t0 = time.time()
d, rows, order, p, q, tasks = load(a.data); N, J = len(rows), len(order); ut = sorted(set(tasks)); T = len(ut)
tidx = np.array([ut.index(t) for t in tasks]); mu_q = q @ GRID
METH = ['constant', 'equal_mixture', 'corr_mixture_pearson', 'ce_mixture', 'val_rps_selected_refit', 'val_rps_selected_fitonly', 'val_ce_selected_refit', 'val_ce_selected_fitonly']
LABEL = {'constant': 'constant (train marginal)', 'equal_mixture': 'equal-weight mixture', 'corr_mixture_pearson': '② mixture maximizing train Pearson (20 train tasks)',
         'ce_mixture': '④ mixture minimizing train CE (20 train tasks, no validation)',
         'val_rps_selected_refit': '③ pick by validation RPS (15 fit / 5 val), refit on all 20',
         'val_rps_selected_fitonly': '③ pick by validation RPS, keep the 15-task fit',
         'val_ce_selected_refit': '③ pick by validation CE, refit on all 20', 'val_ce_selected_fitonly': '③ pick by validation CE, keep the 15-task fit'}

def candidates(idx):
    """Candidate judges fitted from artifacts idx only: name -> (kind, weights or None, marginal). Same family for every method."""
    pt, qt = p[idx], q[idx]; marg = smooth(pt.mean(0), EPS); C = {}
    w_ce, _ = fit(qt, pt, 'ce'); eq = np.full(J, 1/J)
    for lam in SHRINK: C[f'ce_shrink_{lam}'] = ('mix', (1-lam)*w_ce + lam*eq)
    w_p, _ = fit(qt, pt, 'pearson'); C['pearson_mixture'] = ('mix', w_p)
    for j in range(J): C[f'single_{order[j]}'] = ('mix', np.eye(J)[j])
    C['constant'] = ('const', None)
    return C, marg

def predict(c, marg, te):
    kind, w = c
    return np.tile(marg, (len(te), 1)) if kind == 'const' else np.einsum('njr,j->nr', q[te], w)

def run_split(s):
    tr, te = split_tasks(tasks, REPEAT_SEED0 + s)                       # same 20/5 as experiment 12
    rng = np.random.default_rng(777000 + s); trt = sorted(set(tasks[tr])); val_t = set(rng.permutation(trt)[:5].tolist())
    is_val = np.array([t in val_t for t in tasks[tr]]); fit_idx, val_idx = tr[~is_val], tr[is_val]
    out = {}
    # 4 and 2 on all 20 train tasks (as in experiment 12)
    C20, m20 = candidates(tr)
    out['constant'] = predict(C20['constant'], m20, te); out['equal_mixture'] = predict(('mix', np.full(J, 1/J)), m20, te)
    out['corr_mixture_pearson'] = predict(C20['pearson_mixture'], m20, te); out['ce_mixture'] = predict(C20['ce_shrink_0.0'], m20, te)
    # 3: candidates fitted on 15, ranked on the 5 validation tasks, test never touched
    C15, m15 = candidates(fit_idx); picks = {}
    for tag, metric in [('rps', rps), ('ce', ce)]:
        sc = {k: float(metric(p[val_idx], predict(c, m15, val_idx)).mean()) for k, c in C15.items()}
        best = min(sc, key=sc.get); picks[tag] = best
        out[f'val_{tag}_selected_fitonly'] = predict(C15[best], m15, te)
        out[f'val_{tag}_selected_refit'] = predict(C20[best], m20, te)     # same candidate name, refitted on all 20 train tasks
    return s, te, {m: score(p[te], out[m]) for m in METH}, picks

if __name__ == '__main__':
    with Pool(4) as pool: R = pool.map(run_split, range(a.splits), chunksize=10)
    SUM = {mt: {m: np.zeros(N) for m in METH} for mt in ['ce', 'rps', 'tvd']}; CNT = np.zeros(N)
    CSUM = {mt: {m: np.zeros(T) for m in METH} for mt in ['pearson', 'spearman']}; CCNT = {mt: {m: np.zeros(T) for m in METH} for mt in ['pearson', 'spearman']}
    CSPLIT = {mt: {m: [] for m in METH} for mt in ['pearson', 'spearman']}
    pickcount = {'rps': {}, 'ce': {}}
    for s, te, sc_all, picks in R:
        CNT[te] += 1; tt = np.unique(tidx[te])
        for tag in picks: pickcount[tag][picks[tag]] = pickcount[tag].get(picks[tag], 0) + 1
        for m in METH:
            sc = sc_all[m]
            for mt in SUM: SUM[mt][m][te] += sc[mt]
            for mt in CSUM:
                CSPLIT[mt][m].append(sc[mt])
                if np.isfinite(sc[mt]): CSUM[mt][m][tt] += sc[mt]; CCNT[mt][m][tt] += 1
    assert (CNT > 0).all()
    per = {mt: {m: SUM[mt][m]/CNT for m in METH} for mt in SUM}
    tsum = lambda x: (np.bincount(tidx, weights=x, minlength=T), np.bincount(tidx, minlength=T))
    rng = np.random.default_rng(1210); draws = rng.integers(0, T, size=(a.boot, T))
    def boot_paired(diff_t, n_t):
        point = float(diff_t.sum()/n_t.sum()); bs = np.array([diff_t[dr].sum()/n_t[dr].sum() for dr in draws]); lo, hi = np.percentile(bs, [2.5, 97.5])
        return {'point': point, 'ci95': [float(lo), float(hi)], 'excludes_zero': bool(lo > 0 or hi < 0)}
    res = {'n_artifacts': N, 'n_tasks': T, 'splits': a.splits, 'train_tasks': 20, 'fit_tasks_in_3': 15, 'val_tasks_in_3': 5, 'test_tasks': 5, 'bootstrap_draws': a.boot, 'epsilon': EPS,
           'candidate_order': order, 'shrink_grid': SHRINK, 'inference_calls': 0, 'provider_cost_usd': 0, 'labels': LABEL, 'metrics': {}, 'corr_metrics': {}, 'paired': {},
           'selection_counts': pickcount, 'test_count_per_artifact_min_max': [int(CNT.min()), int(CNT.max())]}
    PAIRS = [('val_rps_selected_refit', 'ce_mixture'), ('val_rps_selected_fitonly', 'ce_mixture'), ('val_ce_selected_refit', 'ce_mixture'), ('val_ce_selected_fitonly', 'ce_mixture'),
             ('val_rps_selected_refit', 'corr_mixture_pearson'), ('val_rps_selected_refit', 'constant'), ('val_rps_selected_refit', 'equal_mixture'),
             ('ce_mixture', 'corr_mixture_pearson'), ('ce_mixture', 'constant'), ('ce_mixture', 'equal_mixture')]
    for mt in SUM:
        res['metrics'][mt] = {m: float(per[mt][m].mean()) for m in METH}
        for x, y in PAIRS:
            st, n_t = tsum(per[mt][x]-per[mt][y]); r = boot_paired(st, n_t); r['tasks_first_better'] = int((st < 0).sum()); res['paired'][f'{mt}: {x} minus {y}'] = r
    for mt in CSUM:
        tm = {m: np.where(CCNT[mt][m] > 0, CSUM[mt][m]/np.maximum(CCNT[mt][m], 1), np.nan) for m in METH}
        res['corr_metrics'][mt] = {m: {'mean_over_splits': float(np.nanmean(CSPLIT[mt][m])) if np.isfinite(CSPLIT[mt][m]).any() else None,
                                       'undefined_splits': int(np.isnan(CSPLIT[mt][m]).sum())} for m in METH}
        for x, y in PAIRS[:4] + PAIRS[4:5] + PAIRS[7:8]:
            ok = np.isfinite(tm[x]) & np.isfinite(tm[y]); dt = np.where(ok, tm[x]-tm[y], 0.0); n = ok.astype(float)
            bs = np.array([dt[dr].sum()/max(n[dr].sum(), 1) for dr in draws]); lo, hi = np.percentile(bs, [2.5, 97.5])
            res['paired'][f'{mt} (test-set correlation, task-attributed): {x} minus {y}'] = {'point': float(dt.sum()/n.sum()), 'ci95': [float(lo), float(hi)], 'excludes_zero': bool(lo > 0 or hi < 0)}
    res['seconds'] = time.time()-t0; res['environment'] = {'python': platform.python_version(), 'numpy': np.__version__, 'scipy': scipy.__version__}
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); json.dump(res, open(out/'results.json', 'w'), indent=1)
    print(json.dumps({k: res[k] for k in ['metrics', 'selection_counts', 'seconds']}, indent=1))
    for k, v in res['paired'].items(): print(k, round(v['point'], 4), [round(x, 4) for x in v['ci95']], v['excludes_zero'])
