"""Experiment 18 (big-data version 1): fit the judge on the large AI-rater-labelled pool of VeriBench experiment 106 (fresh artifacts, 50 tasks disjoint from the 75),
test on the 75 human-rated artifacts (25 tasks, 195 expert ratings, never used for fitting or selection). Candidate judges are the four cached configs that exist on
both sets (H0 and H2 on gpt-6-sol-high and claude-opus-5-5, three repeats each, Vals Valkyrie vb103_judge). Zero new model calls, CPU only.
Usage: ~/.venvs/judge/bin/python run_exp18.py --v106 <veribench experiment 106 dir> --human dataset.json --out results [--boot 2000]
Imports shared code from ../../16_formulation3_val_selection_vs_4/scripts."""
import argparse, csv, glob, json, os, sys, time, platform, collections
from pathlib import Path
from multiprocessing import Pool
import numpy as np, scipy
from scipy.stats import rankdata
from scipy.optimize import minimize
sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'16_formulation3_val_selection_vs_4'/'scripts'))
from common import *
from ce_mixture import fit

ap = argparse.ArgumentParser(); ap.add_argument('--v106', required=True); ap.add_argument('--human', required=True); ap.add_argument('--out', required=True)
ap.add_argument('--boot', type=int, default=2000); ap.add_argument('--splits', type=int, default=1000)
a = ap.parse_args(); t0 = time.time(); V = Path(a.v106)/'expt_v5'
CONFIGS = {'H0_sol': 'Z_H0_sol_high', 'H0_opus': 'Z_H0_opus55_max', 'H2_sol': 'F_H2_sol_high', 'H2_opus': 'F_H2_opus55_max'}
HARNESS = {'H0_sol': 'Vals Valkyrie vb103_judge, openai/gpt-6-sol-high, prompt H0 (bare instructions)', 'H0_opus': 'Vals Valkyrie vb103_judge, anthropic/claude-opus-5-5 max, prompt H0',
           'H2_sol': 'Vals Valkyrie vb103_judge, openai/gpt-6-sol-high, prompt H2 (frozen judge)', 'H2_opus': 'Vals Valkyrie vb103_judge, anthropic/claude-opus-5-5 max, prompt H2'}
order = list(CONFIGS); J = len(order)
T = {r['item']: r for r in csv.DictReader(open(V/'results/targets.csv'))}
# judge outputs: score_0_5 of COMPLETE cells, up to 3 repeats per item per config
js = {c: collections.defaultdict(list) for c in order}
for c, run in CONFIGS.items():
    for l in open(V/f'runs/{run}/cells.jsonl'):
        x = json.loads(l)
        if x['category'] == 'COMPLETE' and x.get('score_0_5') not in (None, ''): js[c][x['item']].append(int(x['score_0_5']))
# AI-rater labels: all COMPLETE cells of the six rater families present in the checkout (S1 for the 75, S2 for the fresh groups), all personas/frames and repeats pooled per item
ai = collections.defaultdict(list); fam_present = set()
for run in sorted(glob.glob(str(V/'runs/S[12]_*'))):
    f = run+'/cells.jsonl'
    if not os.path.exists(f): continue
    fam_present.add(os.path.basename(run).split('_', 1)[1])
    for l in open(f):
        x = json.loads(l)
        if x['category'] == 'COMPLETE' and x.get('score_0_5') not in (None, ''): ai[x['item']].append(int(x['score_0_5']))
hum = json.load(open(a.human)); hrows = {r['item']: r for r in hum['rows']}
items_h = [r['item'] for r in hum['rows']]
items_f = [i for i, r in T.items() if r['group'] != 'G00' and r['blank'] == 'False' and i in ai and all(len(js[c].get(i, [])) > 0 for c in order)]
items_h_ok = [i for i in items_h if all(len(js[c].get(i, [])) > 0 for c in order) and i in ai]
audit = {'fresh_non_blank_in_targets': sum(1 for r in T.values() if r['group'] != 'G00' and r['blank'] == 'False'), 'fresh_used': len(items_f), 'human_items': len(items_h), 'human_items_with_all_judges': len(items_h_ok),
         'rater_families_present': sorted(fam_present), 'ai_cells_per_fresh_item_min_median_max': [int(np.min([len(ai[i]) for i in items_f])), float(np.median([len(ai[i]) for i in items_f])), int(np.max([len(ai[i]) for i in items_f]))],
         'repeats_per_judge_per_fresh_item_min': {c: int(min(len(js[c][i]) for i in items_f)) for c in order}}
assert len(items_h_ok) == 75, audit
def build(items, labels_from):
    P = np.array([histogram(labels_from(i)) for i in items]); Q = np.stack([smooth(np.array([histogram(js[c][i]) for i in items]), EPS) for c in order], axis=1)
    return P, Q, np.array([T[i]['task'] if i in T else hrows[i]['task'] for i in items])
Pf, Qf, Tf = build(items_f, lambda i: ai[i])                    # fresh pool, AI-rater label histograms
Ph, Qh, Th = build(items_h, lambda i: hrows[i]['ratings'])      # 75 human-rated, human label histograms
Pa75, _, _ = build(items_h, lambda i: ai[i])                    # the same 75, AI-rater label histograms (control b, reference)
grp_f = np.array([T[i]['group'] for i in items_f])
assert not (set(Tf) & set(Th)), 'task overlap between pool and test'
muf, muh = Qf @ GRID, Qh @ GRID

def fit_rps_mix(Q, P):
    def f(w): pr = np.einsum('njr,j->nr', Q, w); return float(rps(P, pr).mean())
    r = minimize(f, np.full(J, 1/J), method='SLSQP', bounds=[(0, 1)]*J, constraints={'type': 'eq', 'fun': lambda w: w.sum()-1}, options={'ftol': 1e-12, 'maxiter': 500})
    w = np.maximum(r.x, 0); return w/w.sum()

def fit_head(Q, P, w):
    """temperature tau and per-rating bias b on the log of the CE mixture, fitted by CE on the training labels (7 parameters)."""
    base = np.log(np.einsum('njr,j->nr', Q, w))
    def f(th):
        z = th[0]*base + th[1:]; z -= z.max(1, keepdims=True); lg = z - np.log(np.exp(z).sum(1, keepdims=True)); return -float((P*lg).sum(1).mean())
    r = minimize(f, np.r_[1.0, np.zeros(6)], method='L-BFGS-B'); return r.x

def head_pred(Q, w, th):
    z = th[0]*np.log(np.einsum('njr,j->nr', Q, w)) + th[1:]; z -= z.max(1, keepdims=True); e = np.exp(z); return e/e.sum(1, keepdims=True)

METH = ['constant', 'equal_mixture', 'corr_single', 'corr_mixture_pearson', 'corr_mixture_spearman', 'ce_single', 'ce_mixture', 'rps_mixture', 'ce_mixture_head']
LABEL = {'constant': 'constant (pool marginal)', 'equal_mixture': 'equal-weight mixture', 'corr_single': '② best single judge by pool Pearson', 'corr_mixture_pearson': '② mixture maximizing pool Pearson',
         'corr_mixture_spearman': '② mixture maximizing pool Spearman (4,000-point simplex search)', 'ce_single': '④ best single judge by pool CE', 'ce_mixture': '④ mixture minimizing pool CE',
         'rps_mixture': '④ mixture minimizing pool RPS', 'ce_mixture_head': '④ CE mixture plus temperature and rating bias (exploratory)'}

def fit_all(Q, P, rng):
    mu = Q @ GRID; hm = P @ GRID; W = {}
    W['constant'] = ('const', smooth(P.mean(0), EPS)); W['equal_mixture'] = ('mix', np.full(J, 1/J))
    pe = np.nan_to_num([pearson(mu[:, j], hm) for j in range(J)], nan=-2); W['corr_single'] = ('mix', np.eye(J)[int(np.argmax(pe))])
    W['corr_mixture_pearson'] = ('mix', fit(Q, P, 'pearson')[0])
    cand = np.vstack([np.eye(J), np.full((1, J), 1/J), rng.dirichlet(np.ones(J), size=4000)])
    rk = rankdata(mu @ cand.T, axis=0); rt = rankdata(hm); rk -= rk.mean(0); rtc = rt - rt.mean(); den = np.linalg.norm(rk, axis=0)*np.linalg.norm(rtc)
    sp = np.where(den > 1e-12, (rk*rtc[:, None]).sum(0)/np.where(den > 1e-12, den, 1), -2); best = cand[int(np.argmax(sp))]
    W['corr_mixture_spearman'] = ('mix', best)
    W['ce_single'] = ('mix', np.eye(J)[int(np.argmin([ce(P, Q[:, j]).mean() for j in range(J)]))])
    wce = fit(Q, P, 'ce')[0]; W['ce_mixture'] = ('mix', wce); W['rps_mixture'] = ('mix', fit_rps_mix(Q, P)); W['ce_mixture_head'] = ('head', (wce, fit_head(Q, P, wce)))
    return W

def predict(W, m, Q):
    k, w = W[m]
    if k == 'const': return np.tile(w, (len(Q), 1))
    if k == 'mix': return np.einsum('njr,j->nr', Q, w)
    return head_pred(Q, *w)

def evaluate(W, Q, P):
    out = {}
    for m in METH:
        Qm = predict(W, m, Q); out[m] = score(P, Qm)
    return out

# ---- main fit on all fresh items, test on the 75 humans
rng0 = np.random.default_rng(20261211); W = fit_all(Qf, Pf, rng0); EV = evaluate(W, Qh, Ph)
Ut = sorted(set(Th)); tid = np.array([Ut.index(t) for t in Th]); NT = len(Ut)
pa = lambda ev, mt: {m: ev[m][mt] for m in METH}
res = {'audit': audit, 'configs': HARNESS, 'candidate_order': order, 'labels': LABEL, 'n_pool_items': len(items_f), 'n_pool_tasks': len(set(Tf)), 'n_test_items': 75, 'n_test_tasks': NT,
       'inference_calls': 0, 'provider_cost_usd': 0, 'epsilon': EPS, 'weights': {m: (W[m][1].tolist() if W[m][0] == 'mix' else (None if W[m][0] == 'const' else {'w': W[m][1][0].tolist(), 'tau_bias': W[m][1][1].tolist()})) for m in METH},
       'test_on_75_humans': {mt: {m: float(np.mean(EV[m][mt])) if hasattr(EV[m][mt], '__len__') else float(EV[m][mt]) for m in METH} for mt in ['rps', 'ce', 'tvd', 'pearson', 'spearman']}}
# single judges as reference (not selected on test)
res['single_judges_on_75_humans'] = {}
for j, c in enumerate(order):
    s = score(Ph, Qh[:, j]); res['single_judges_on_75_humans'][c] = {k: float(np.mean(v)) for k, v in s.items()}
# AI-panel label itself as a forecast of the human distribution (reference, uses the 75's AI labels, so not a deployable judge)
s = score(Ph, smooth(Pa75, EPS)); res['ai_panel_label_as_forecast_of_humans_on_75'] = {k: float(np.mean(v)) for k, v in s.items()}
res['human_vs_ai_mean_rating_gap_on_75'] = {'human_mean': float((Ph@GRID).mean()), 'ai_panel_mean': float((Pa75@GRID).mean()), 'pool_ai_mean': float((Pf@GRID).mean())}
# joint bootstrap: resample pool tasks (refit everything) and test tasks
Uf = sorted(set(Tf)); idx_by_task = {t: np.flatnonzero(Tf == t) for t in Uf}; BR = np.random.default_rng(1210)
def one_boot(seed):
    r = np.random.default_rng(seed); tf = r.integers(0, len(Uf), size=len(Uf)); ii = np.concatenate([idx_by_task[Uf[k]] for k in tf]); Wb = fit_all(Qf[ii], Pf[ii], r)
    tt = r.integers(0, NT, size=NT); jj = np.concatenate([np.flatnonzero(tid == k) for k in tt]); evb = evaluate(Wb, Qh[jj], Ph[jj])
    return {m: {mt: float(np.mean(evb[m][mt])) if hasattr(evb[m][mt], '__len__') else float(evb[m][mt]) for mt in ['rps', 'ce', 'tvd', 'pearson', 'spearman']} for m in METH}
if __name__ == '__main__':
    with Pool(4) as pool: B = pool.map(one_boot, range(5000, 5000+a.boot), chunksize=5)
    def ci(vals): v = np.array(vals, float); v = v[np.isfinite(v)]; return [float(np.percentile(v, 2.5)), float(np.percentile(v, 97.5))] if len(v) else None
    res['bootstrap_draws'] = a.boot; res['test_on_75_humans_ci95'] = {mt: {m: ci([b[m][mt] for b in B]) for m in METH} for mt in ['rps', 'ce', 'tvd', 'pearson', 'spearman']}
    PAIRS = [('ce_mixture', 'corr_mixture_pearson'), ('rps_mixture', 'corr_mixture_pearson'), ('ce_mixture', 'corr_mixture_spearman'), ('ce_single', 'corr_single'), ('ce_mixture_head', 'corr_mixture_pearson'),
             ('ce_mixture', 'constant'), ('ce_mixture', 'equal_mixture'), ('corr_mixture_pearson', 'equal_mixture'), ('rps_mixture', 'equal_mixture')]
    res['paired_on_75_humans'] = {}
    for mt in ['rps', 'ce', 'tvd', 'pearson', 'spearman']:
        for x, y in PAIRS:
            dv = [b[x][mt]-b[y][mt] for b in B]; pt = float(np.mean(EV[x][mt])-np.mean(EV[y][mt])); lo_hi = ci(dv)
            res['paired_on_75_humans'][f'{mt}: {x} minus {y}'] = {'point': pt, 'ci95': lo_hi, 'excludes_zero': bool(lo_hi and (lo_hi[0] > 0 or lo_hi[1] < 0))}
    # control (b): same fit on groups G01-G10, scored against the AI-rater labels of held-out fresh groups G11-G13 and of the 75 (label shift versus judge quality)
    trn = np.isin(grp_f, [f'G{k:02d}' for k in range(1, 11)]); tst = ~trn; Wb = fit_all(Qf[trn], Pf[trn], np.random.default_rng(7))
    res['control_b_train_G01_G10_AI_labels'] = {'n_train': int(trn.sum()), 'n_heldout_fresh': int(tst.sum()),
        'rps_on_heldout_fresh_AI_labels': {m: float(np.mean(evaluate(Wb, Qf[tst], Pf[tst])[m]['rps'])) for m in METH}, 'rps_on_75_AI_labels': {m: float(np.mean(evaluate(Wb, Qh, smooth(Pa75, 1e-12))[m]['rps'])) for m in METH},
        'rps_on_75_human_labels': {m: float(np.mean(evaluate(Wb, Qh, Ph)[m]['rps'])) for m in METH}}
    # control (a): fit on the 75 humans only with the same four judge configs and the experiment 12 split rule (20/5 tasks, 1000 splits), RPS on test tasks
    def split_run(s):
        tr, te = split_tasks(Th, REPEAT_SEED0+s); Wc = fit_all(Qh[tr], Ph[tr], np.random.default_rng(s)); return te, {m: score(Ph[te], predict(Wc, m, Qh[te]))['rps'] for m in METH}
    with Pool(4) as pool: S = pool.map(split_run, range(a.splits), chunksize=10)
    sm = {m: np.zeros(75) for m in METH}; cn = np.zeros(75)
    for te, d in S:
        cn[te] += 1
        for m in METH: sm[m][te] += d[m]
    per = {m: sm[m]/cn for m in METH}; nt = np.bincount(tid, minlength=NT).astype(float); dr = BR.integers(0, NT, size=(5000, NT))
    def tci(x): xt = np.bincount(tid, weights=x, minlength=NT); bs = [xt[r].sum()/nt[r].sum() for r in dr]; return {'point': float(xt.sum()/nt.sum()), 'ci95': [float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))]}
    res['control_a_fit_on_75_humans_only_20_5_splits_rps'] = {'splits': a.splits, 'metrics': {m: tci(per[m]) for m in METH},
        'ce_mixture minus corr_mixture_pearson': tci(per['ce_mixture']-per['corr_mixture_pearson']), 'ce_mixture minus equal_mixture': tci(per['ce_mixture']-per['equal_mixture'])}
    res['seconds'] = time.time()-t0; res['environment'] = {'python': platform.python_version(), 'numpy': np.__version__, 'scipy': scipy.__version__}
    o = Path(a.out); o.mkdir(parents=True, exist_ok=True); json.dump(res, open(o/'results.json', 'w'), indent=1)
    print(json.dumps(audit, indent=1)); print('weights', json.dumps(res['weights'])[:1500])
    for mt in ['rps', 'ce', 'tvd', 'pearson', 'spearman']:
        print(mt); [print(f'  {m:24s} {res["test_on_75_humans"][mt][m]:.4f} {res["test_on_75_humans_ci95"][mt][m]}') for m in METH]
    for k, v in res['paired_on_75_humans'].items():
        if k.startswith('rps') or k.startswith('ce:'): print(k, round(v['point'], 4), v['ci95'], v['excludes_zero'])
    print('singles', json.dumps(res['single_judges_on_75_humans'])); print('ai-label forecast', res['ai_panel_label_as_forecast_of_humans_on_75'], res['human_vs_ai_mean_rating_gap_on_75'])
    print('ctrl b', json.dumps(res['control_b_train_G01_G10_AI_labels'])); print('ctrl a', json.dumps(res['control_a_fit_on_75_humans_only_20_5_splits_rps']))
