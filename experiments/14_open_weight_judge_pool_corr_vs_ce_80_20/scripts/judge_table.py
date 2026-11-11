"""Per-judge in-sample table (all 75 artifacts, no fitting) -> results/judge_table.json.  Usage: python judge_table.py dataset_pool.json results/judge_table.json"""
import sys, json, numpy as np
from common import *
d, rows, order, p, q, tasks = load(sys.argv[1]); old = set(json.load(open(sys.argv[1]))['candidate_order'][:5]); hm = p @ GRID; out = []
for j, n in enumerate(order):
    Q = q[:, j]; mu = Q @ GRID
    out.append({'name': n, 'source': 'cached frontier (Sol/Opus)' if j < 5 else 'open-weight, vLLM, T=0.7', 'rps': float(rps(p, Q).mean()), 'ce': float(ce(p, Q).mean()), 'tvd': float(tvd(p, Q).mean()),
                'spearman': spearman(mu, hm), 'pearson': pearson(mu, hm), 'mean_rating': float((mu*5).mean())})
json.dump({'judges': out}, open(sys.argv[2], 'w'), indent=1); print(len(out))
