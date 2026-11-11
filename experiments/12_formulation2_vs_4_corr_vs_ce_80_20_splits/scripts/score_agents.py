"""Score the two agent-chosen judges (one picked with correlation as the only objective, one with CE) on the fixed split's 5 held-out test tasks.
Usage: ~/.venvs/judge/bin/python score_agents.py --data dataset.json --specs DIR --out results/fixed_split_agents.json"""
import argparse, json
from common import *
ap = argparse.ArgumentParser(); ap.add_argument('--data', required=True); ap.add_argument('--specs', required=True); ap.add_argument('--out', required=True); a = ap.parse_args()
d, rows, order, p, q, tasks = load(a.data); tr, te = split_tasks(tasks, FIXED_SEED)
marg = smooth(p[tr].mean(0), EPS); out = {'test_tasks': sorted(set(tasks[te])), 'agents': {}}
for name in ['corr', 'ce']:
    s = json.load(open(f'{a.specs}/spec_{name}.json')); w = s['weights']
    Q = sum(w[n]*q[te][:, j] for j, n in enumerate(order)) + w['train_marginal']*marg
    Q = smooth(Q/Q.sum(1, keepdims=True), 0)
    sc = score(p[te], Q); out['agents'][name] = {'weights': w, 'how_chosen': s['how_chosen'], 'test': {k: float(np.mean(v)) for k, v in sc.items()},
        'per_task': {t: {k: float(sc[k][tasks[te] == t].mean()) for k in ['ce', 'rps', 'tvd']} for t in sorted(set(tasks[te]))}}
json.dump(out, open(a.out, 'w'), indent=1); print(json.dumps({k: v['test'] for k, v in out['agents'].items()}, indent=1))
