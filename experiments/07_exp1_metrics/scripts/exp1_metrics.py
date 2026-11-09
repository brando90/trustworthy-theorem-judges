#!/usr/bin/env python3
"""TLDR: Experiment 1 metric table on cached scalar judge scores (no model calls): nRMSE, sqrt RPS, KL, constant nRMSE, Pearson, Spearman, Kendall, 10,000-resample task-level bootstrap.

Reads the private dataset.json written by experiments/06_*/scripts/import_cached.py (per-item ratings are not published).
Writes aggregate-only JSON. No R^2. One probability floor EPS=1e-3. Judge pmf = histogram of the 3 sampled repeats (no digit logprobs exist).
"""
import argparse, json, itertools
import numpy as np

EPS = 1e-3
B = 10000
SEED = 20261109
FAMILIES = {'nrmse': 'lower', 'sqrt_rps': 'lower', 'kl': 'lower', 'pearson': 'higher', 'spearman': 'higher', 'kendall': 'higher'}


def human_matrix(ds, panel, items_jsonl):
    byitem = {}
    for l in open(items_jsonl):
        if l.strip():
            r = json.loads(l); byitem[r['item']] = r
    cols = ['p1', 'p2', 'p3'] if panel == 'expert' else ['p1', 'p2', 'p3', 'p4', 'p5']
    H = np.full((len(ds['rows']), 5), np.nan)
    for i, r in enumerate(ds['rows']):
        for c, k in enumerate(cols):
            v = byitem[r['item']][k]
            if v is not None: H[i, c] = v
    return H


def item_quantities(J, H):
    """J: (items, 3) integer judge scores. H: (items, 5) human ratings with NaN. Returns per-item arrays."""
    n = J.shape[0]
    jc = np.stack([(J == r).sum(1) for r in range(6)], 1).astype(float)  # counts of judge repeats per rating
    p = jc / jc.sum(1, keepdims=True)
    p = np.maximum(p, EPS); p = p / p.sum(1, keepdims=True)  # one floor, renormalised
    q = np.stack([(H == r).sum(1) for r in range(6)], 1).astype(float)
    q = q / q.sum(1, keepdims=True)
    with np.errstate(divide='ignore', invalid='ignore'):
        kl = np.where(q > 0, q * np.log(q / p), 0.0).sum(1)
        ce = np.where(q > 0, -q * np.log(p), 0.0).sum(1)
    Fp = np.cumsum(p, 1)[:, :5]; Fq = np.cumsum(q, 1)[:, :5]
    rps = ((Fp - Fq) ** 2).sum(1) / 5.0
    jmean = J.mean(1) / 5.0
    hmean = np.nanmean(H, 1) / 5.0
    return dict(kl=kl, ce=ce, rps=rps, j=jmean, h=hmean, q=q)


def sgn_matrix(x):
    d = x[:, None] - x[None, :]
    return np.sign(d)


def point_and_boot(quant, task_of, rng, mask, B=B, extra_const=True):
    """quant: dict per judge of item_quantities. mask: items included. Returns point estimates and bootstrap draws (B, judge, metric)."""
    items = np.where(mask)[0]
    tasks = sorted(set(task_of[items]))
    by_task = [items[task_of[items] == t] for t in tasks]
    nt = len(tasks)
    # bootstrap index lists: resample tasks with replacement
    draws = rng.integers(0, nt, size=(B, nt))
    names = list(quant)
    h = quant[names[0]]['h']
    Sh = sgn_matrix(h)
    Sj = {n: sgn_matrix(quant[n]['j']) for n in names}
    from scipy.stats import rankdata
    metric_names = ['nrmse', 'sqrt_rps', 'kl', 'const_nrmse', 'pearson', 'spearman', 'kendall']
    out = np.full((B + 1, len(names), len(metric_names)), np.nan)  # row 0 = point estimate

    def compute(idx, row):
        hh = h[idx]
        c = hh.mean()
        const = np.sqrt(((hh - c) ** 2).mean())
        hr = rankdata(hh)
        Sh_i = Sh[np.ix_(idx, idx)]
        for a, n in enumerate(names):
            qn = quant[n]
            jj = qn['j'][idx]
            nr = np.sqrt(((jj - hh) ** 2).mean())
            rp = np.sqrt(qn['rps'][idx].mean())
            kl = qn['kl'][idx].mean()
            pe = np.corrcoef(jj, hh)[0, 1] if jj.std() > 0 and hh.std() > 0 else np.nan
            jr = rankdata(jj)
            sp = np.corrcoef(jr, hr)[0, 1] if jr.std() > 0 and hr.std() > 0 else np.nan
            Sj_i = Sj[n][np.ix_(idx, idx)]
            den = np.sqrt((Sj_i ** 2).sum() * (Sh_i ** 2).sum())
            ke = (Sj_i * Sh_i).sum() / den if den > 0 else np.nan
            out[row, a] = [nr, rp, kl, const, pe, sp, ke]

    compute(items, 0)
    for b in range(B):
        idx = np.concatenate([by_task[t] for t in draws[b]])
        compute(idx, b + 1)
    return names, metric_names, out


def summarize(names, metric_names, out):
    res = {}
    for a, n in enumerate(names):
        res[n] = {}
        for m, mn in enumerate(metric_names):
            col = out[1:, a, m]
            res[n][mn] = dict(point=float(out[0, a, m]), lo=float(np.nanpercentile(col, 2.5)), hi=float(np.nanpercentile(col, 97.5)), n_nan=int(np.isnan(col).sum()))
    return res


def ranking_analysis(names, metric_names, out):
    fam = [m for m in metric_names if m in FAMILIES]
    sign = {m: (1 if FAMILIES[m] == 'lower' else -1) for m in fam}
    mi = {m: metric_names.index(m) for m in fam}
    pt = {m: [out[0, a, mi[m]] * sign[m] for a in range(len(names))] for m in fam}
    order = {m: [names[i] for i in np.argsort(pt[m], kind='stable')] for m in fam}
    # P(rank 1) per metric by bootstrap
    p1 = {}
    for m in fam:
        v = out[1:, :, mi[m]] * sign[m]
        v = np.where(np.isnan(v), np.inf, v)
        best = np.argmin(v, 1)
        p1[m] = {names[a]: float((best == a).mean()) for a in range(len(names))}
    # paired differences between judges: CI excludes zero?
    pairs = {}
    for m in fam:
        pairs[m] = {}
        for a, b in itertools.combinations(range(len(names)), 2):
            d = out[1:, a, mi[m]] - out[1:, b, mi[m]]
            lo, hi = np.nanpercentile(d, [2.5, 97.5])
            pairs[m][f'{names[a]} - {names[b]}'] = dict(point=float(out[0, a, mi[m]] - out[0, b, mi[m]]), lo=float(lo), hi=float(hi), excludes_zero=bool(lo > 0 or hi < 0))
    # Kendall tau between families' rankings (points)
    from scipy.stats import kendalltau
    taus = {}
    for m1, m2 in itertools.combinations(fam, 2):
        taus[f'{m1} vs {m2}'] = float(kendalltau(pt[m1], pt[m2]).statistic)
    return dict(order_best_to_worst=order, p_rank1=p1, paired=pairs, tau_between_metric_rankings=taus)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--private', required=True, help='dir holding dataset.json and source/ from import_cached.py')
    ap.add_argument('--out', required=True)
    ap.add_argument('--boot', type=int, default=B)
    a = ap.parse_args()
    ds = json.load(open(f'{a.private}/dataset.json'))
    items_jsonl = f'{a.private}/source/experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test/inputs/items.jsonl'
    rows = ds['rows']
    task_of = np.array([r['task'] for r in rows])
    split_of = np.array([r['split'] for r in rows])
    names = list(ds['outputs'])
    results = {'eps': EPS, 'bootstrap': a.boot, 'seed': SEED, 'judge_probability_source': 'histogram of 3 sampled repeats (no digit logprobs in the cached receipts)',
               'kl_target': 'forward KL(q||p), q = empirical pmf of the 2-3 human ratings per item (expert panel); CE = KL + H(q) is also stored per variant', 'variants': {}}
    variants = [('expert_all75', 'expert', np.ones(len(rows), bool)),
                ('expert_valtest', 'expert', split_of != 'train'),
                ('all5_all75', 'all5', np.ones(len(rows), bool))]
    for vname, panel, mask in variants:
        rng = np.random.default_rng(SEED)
        H = human_matrix(ds, panel, items_jsonl)
        quant = {}
        for n in names:
            J = np.array(ds['outputs'][n])
            quant[n] = item_quantities(J, H)
        m = mask
        nm, mn, out = point_and_boot(quant, task_of, rng, m, B=a.boot)
        summ = summarize(nm, mn, out)
        ce_point = {n: float(quant[n]['ce'][m].mean()) for n in names}
        results['variants'][vname] = dict(panel=panel, n_items=int(m.sum()), n_tasks=int(len(set(task_of[m]))), n_ratings=int((~np.isnan(H[m])).sum()),
                                          metrics=summ, ce_point=ce_point, ranking=ranking_analysis(nm, mn, out))
        print(vname, 'done', flush=True)
    json.dump(results, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
