import json, sys
import numpy as np
from scipy import stats, optimize

D = './'
data = json.load(open(D + 'qa_input.json'))
B = np.arange(6)
FLOOR = 1e-6


def hist(vals):
    h = np.bincount(np.asarray(vals, dtype=int), minlength=6)[:6].astype(float)
    return h / h.sum()


def floorn(q):
    q = np.maximum(np.asarray(q, float), FLOOR)
    return q / q.sum()


def rps(P, Q):
    CP = np.cumsum(P, -1)[..., :5]; CQ = np.cumsum(Q, -1)[..., :5]
    return np.mean((CQ - CP) ** 2 + CP * (1 - CP), -1)


def ce(P, Q):
    Qf = np.maximum(Q, FLOOR); Qf = Qf / Qf.sum(-1, keepdims=True)
    t = np.where(P > 0, -P * np.log(Qf), 0.0)
    return t.sum(-1)


def tvd(P, Q):
    return 0.5 * np.abs(P - Q).sum(-1)


issues = []
# ---- Task 3 leakage checks ----
assert len(data) == 175, len(data)
for a in data:
    for r in a['ratings'] + a['astra'] + a['opus']:
        if not (isinstance(r, int) and 0 <= r <= 5):
            issues.append(f"out-of-range/non-int score in {a['id']}: {r}")
task_splits = {}
for a in data:
    task_splits.setdefault(a['task'], set()).add(a['split'])
multi = {t: sorted(s) for t, s in task_splits.items() if len(s) > 1}
task_sets = {}
for a in data:
    task_sets.setdefault(a['task'], set()).add(a['set'])
multi_set = {t: sorted(s) for t, s in task_sets.items() if len(s) > 1}
few = [a['id'] for a in data if len(a['ratings']) < 1]
ids_dup = len(data) - len({a['id'] for a in data})
fq_bad = []
fq_present_nontest = [a['id'] for a in data if a['split'] != 'test' and 'final_Q' in a]
fq_missing_test = [a['id'] for a in data if a['split'] == 'test' and 'final_Q' not in a]
h3_missing = [a['id'] for a in data if a.get('h3_score') is None or a.get('h3_expected') is None]
rep_bad = [a['id'] for a in data if len(a['astra']) != 3 or len(a['opus']) != 3]
for a in data:
    if 'final_Q' in a:
        q = np.array(a['final_Q'])
        if len(q) != 6 or abs(q.sum() - 1) > 1e-6 or (q < 0).any():
            fq_bad.append((a['id'], float(q.sum()), len(q)))
counts = {}
for sp in ['train', 'val', 'test']:
    for st in ['old', 'new']:
        sub = [a for a in data if a['split'] == sp and a['set'] == st]
        counts[f'{sp}/{st}'] = {'artifacts': len(sub), 'tasks': len({a['task'] for a in sub})}
    sub = [a for a in data if a['split'] == sp]
    counts[f'{sp}/all'] = {'artifacts': len(sub), 'tasks': len({a['task'] for a in sub})}
leak = dict(tasks_in_multiple_splits=multi, tasks_in_multiple_sets=multi_set,
            artifacts_with_lt1_rating=few, duplicate_ids=ids_dup,
            final_Q_bad_sum_or_shape=fq_bad, final_Q_on_nontest=fq_present_nontest,
            final_Q_missing_on_test=fq_missing_test, h3_missing=h3_missing,
            judge_repeat_count_not_3=rep_bad,
            max_abs_final_Q_sum_minus_1=float(max(abs(sum(a['final_Q']) - 1) for a in data if 'final_Q' in a)),
            n_ratings_distribution={int(k): int(v) for k, v in zip(*np.unique([len(a['ratings']) for a in data], return_counts=True))},
            counts=counts,
            passed=(not multi and not few and not fq_bad and not fq_missing_test and ids_dup == 0))
if multi: issues.append(f'LEAKAGE: tasks in multiple splits: {multi}')

# ---- Forecasts ----
P_all = np.array([hist(a['ratings']) for a in data])
hm_all = np.array([np.mean(a['ratings']) for a in data])
trv = [i for i, a in enumerate(data) if a['split'] in ('train', 'val')]
const = {}
for st in ['old', 'new']:
    rr = [r for i in trv if data[i]['set'] == st for r in data[i]['ratings']]
    const[st] = floorn(hist(rr))
pooled = floorn(hist([r for i in trv for r in data[i]['ratings']]))
uni = np.full(6, 1 / 6)

test = [i for i, a in enumerate(data) if a['split'] == 'test']
P = P_all[test]; hm = hm_all[test]
sets = np.array([data[i]['set'] for i in test])
tasks = np.array([data[i]['task'] for i in test])
F = {
    'final_Q': np.array([data[i]['final_Q'] for i in test], float),
    'constant_per_set': np.array([const[data[i]['set']] for i in test]),
    'pooled_constant': np.tile(pooled, (len(test), 1)),
    'uniform': np.tile(uni, (len(test), 1)),
    'H2_judge': np.array([floorn(hist(data[i]['astra'] + data[i]['opus'])) for i in test]),
}

# ---- Task 4 refit ----
def feats(a):
    return [np.mean(a['astra']), np.mean(a['opus']), a['h3_score'], a['h3_expected']]
X_all = np.array([feats(a) for a in data], float)
mu = X_all[trv].mean(0); sd = X_all[trv].std(0, ddof=1)
sd0 = X_all[trv].std(0, ddof=0)
Z_all = (X_all - mu) / sd


def model_probs(params, Z):
    w = params[:4]
    th = np.cumsum(np.concatenate([[params[4]], np.exp(params[5:])]))  # increasing
    eta = th[None, :] - (Z @ w)[:, None]
    C = 1 / (1 + np.exp(-eta))
    C = np.concatenate([np.zeros((len(Z), 1)), C, np.ones((len(Z), 1))], 1)
    return np.diff(C, axis=1)


def obj(params, Z, Pt):
    Q = np.maximum(model_probs(params, Z), 1e-300)
    return np.mean(np.sum(np.where(Pt > 0, -Pt * np.log(Q), 0.0), 1))


Ztr, Ptr = Z_all[trv], P_all[trv]
best = None
funs = []
for s in range(20):
    rng0 = np.random.default_rng(s)
    x0 = np.concatenate([rng0.normal(0, 1, 4), [rng0.normal(-2, 1)], rng0.normal(0, 0.5, 4)])
    r = optimize.minimize(obj, x0, args=(Ztr, Ptr), method='BFGS', options={'gtol': 1e-10, 'maxiter': 20000})
    r = optimize.minimize(obj, r.x, args=(Ztr, Ptr), method='Nelder-Mead', options={'xatol': 1e-10, 'fatol': 1e-12, 'maxiter': 40000})
    r = optimize.minimize(obj, r.x, args=(Ztr, Ptr), method='BFGS', options={'gtol': 1e-10, 'maxiter': 20000})
    funs.append(r.fun)
    if best is None or r.fun < best.fun:
        best = r
F['refit_ordinal'] = model_probs(best.x, Z_all[test])
theta = np.cumsum(np.concatenate([[best.x[4]], np.exp(best.x[5:])]))
refit_info = dict(train_val_mean_CE=float(best.fun), restart_obj_range=[float(min(funs)), float(max(funs))],
                  w=best.x[:4].tolist(), theta=theta.tolist(),
                  feature_mean=mu.tolist(), feature_sd_ddof1=sd.tolist())
Z0 = (X_all - mu) / sd0
r0 = optimize.minimize(obj, np.concatenate([best.x[:4] * sd0 / sd, best.x[4:]]), args=(Z0[trv], Ptr), method='BFGS', options={'gtol': 1e-10})
Q0 = model_probs(r0.x, Z0[test])
refit_info['ddof0_max_abs_pred_diff'] = float(np.abs(Q0 - F['refit_ordinal']).max())
refit_info['max_abs_diff_vs_final_Q'] = float(np.abs(F['refit_ordinal'] - F['final_Q']).max())
refit_info['mean_abs_diff_vs_final_Q'] = float(np.abs(F['refit_ordinal'] - F['final_Q']).mean())

# ---- Task 1 ----
subsets = {'pooled': np.ones(len(test), bool), 'old': sets == 'old', 'new': sets == 'new'}
res1 = {}
for name, Q in F.items():
    res1[name] = {}
    m_rps, m_ce, m_tvd = rps(P, Q), ce(P, Q), tvd(P, Q)
    fm = Q @ B
    for sn, m in subsets.items():
        d = dict(n=int(m.sum()), RPS=float(m_rps[m].mean()), CE=float(m_ce[m].mean()), TVD=float(m_tvd[m].mean()))
        if name not in ('constant_per_set', 'pooled_constant', 'uniform'):
            if np.std(fm[m]) > 0 and np.std(hm[m]) > 0:
                d['spearman'] = float(stats.spearmanr(fm[m], hm[m]).correlation)
                d['pearson'] = float(stats.pearsonr(fm[m], hm[m])[0])
            else:
                d['spearman'] = d['pearson'] = None
        res1[name][sn] = d

# ---- Task 2 bootstrap ----
utasks = sorted(set(tasks))
task_idx = [np.where(tasks == t)[0] for t in utasks]
per = {name: dict(RPS=rps(P, Q), CE=ce(P, Q), TVD=tvd(P, Q)) for name, Q in F.items()}
rng = np.random.default_rng(20261124)
draws = [rng.integers(0, len(utasks), len(utasks)) for _ in range(10000)]
res2 = {}
for other in ['constant_per_set', 'H2_judge']:
    res2[f'final_Q_minus_{other}'] = {}
    for met in ['RPS', 'CE', 'TVD']:
        diff = per['final_Q'][met] - per[other][met]
        pt = float(diff.mean())
        bs = np.empty(10000)
        for b, s in enumerate(draws):
            idx = np.concatenate([task_idx[j] for j in s])
            bs[b] = diff[idx].mean()
        lo, hi = np.percentile(bs, [2.5, 97.5])
        res2[f'final_Q_minus_{other}'][met] = dict(point=pt, ci95=[float(lo), float(hi)], excludes_0=bool(lo > 0 or hi < 0))

out = dict(task1_test_metrics=res1, task2_paired_bootstrap=res2,
           bootstrap_info=dict(n_test_tasks=len(utasks), draws=10000, seed=20261124,
                               unit='task; one draw sequence shared across all comparisons; artifact means over resampled artifacts'),
           task3_leakage=leak, task4_refit=refit_info,
           task4_comparison={'refit': res1['refit_ordinal']['pooled'], 'final_Q': res1['final_Q']['pooled'],
                             'abs_diff': {k: abs(res1['refit_ordinal']['pooled'][k] - res1['final_Q']['pooled'][k]) for k in ['RPS', 'CE', 'TVD']}},
           constants=dict(old=const['old'].tolist(), new=const['new'].tolist(), pooled=pooled.tolist()),
           issues=issues)
json.dump(out, open(D + 'qa_result.json', 'w'), indent=2)

print(f"{'forecast':18s} {'subset':6s} {'n':>3s} {'RPS':>7s} {'CE':>7s} {'TVD':>7s} {'Spear':>7s} {'Pears':>7s}")
for name, r in res1.items():
    for sn, d in r.items():
        sp = d.get('spearman'); pe = d.get('pearson')
        print(f"{name:18s} {sn:6s} {d['n']:3d} {d['RPS']:7.4f} {d['CE']:7.4f} {d['TVD']:7.4f} "
              f"{(f'{sp:7.3f}' if sp is not None else '      -')} {(f'{pe:7.3f}' if pe is not None else '      -')}")
print()
for k, v in res2.items():
    for met, d in v.items():
        print(f"{k:32s} {met:4s} {d['point']:+.4f} [{d['ci95'][0]:+.4f}, {d['ci95'][1]:+.4f}]")
print()
print(json.dumps(leak, default=str))
print(json.dumps(refit_info))
print(json.dumps(out['constants']))
print('issues:', issues)
