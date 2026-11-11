"""Check: NNLS Pearson solver equals the experiment-3 enumeration solver (same optimal training Pearson) on random 5-judge training sets of the cached dataset."""
import sys, json, numpy as np
sys.path.insert(0, '.')
from common import *
from ce_mixture import fit
from nnls_pearson import fit_pearson
d, rows, order, p, q, tasks = load(sys.argv[1]); q5 = q[:, :5]; worst = 0
for s in range(200):
    tr, te = split_tasks(tasks, REPEAT_SEED0 + s)
    w1, r1 = fit(q5[tr], p[tr], 'pearson'); w2, r2 = fit_pearson(q5[tr], p[tr])
    hm = p[tr] @ GRID; r = lambda w: pearson(np.einsum('njr,j->nr', q5[tr], w) @ GRID, hm)
    worst = max(worst, abs(r(w1) - r(w2)))
print('max |train Pearson difference| over 200 splits:', worst)
