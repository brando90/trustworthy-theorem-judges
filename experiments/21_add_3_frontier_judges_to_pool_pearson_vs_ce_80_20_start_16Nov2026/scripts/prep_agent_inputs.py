"""Write the train-only file the optimizing agents see for the fixed split (no test artifact, no test task name).
Usage: ~/.venvs/judge/bin/python prep_agent_inputs.py --data dataset.json --out DIR"""
import argparse, json
from pathlib import Path
from common import *
ap = argparse.ArgumentParser(); ap.add_argument('--data', required=True); ap.add_argument('--out', required=True); a = ap.parse_args()
d, rows, order, p, q, tasks = load(a.data); tr, te = split_tasks(tasks, FIXED_SEED)
out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
train = [{'artifact': int(i), 'task': rows[i]['task'], 'human_ratings_0to5': rows[i]['ratings'],
          'judge_cached_scalar_ratings_0to5': {n: d['outputs'][n][i] for n in order}} for i in tr]
json.dump({'candidate_judges': order, 'train': train}, open(out/'train_only.json', 'w'), indent=1)
print('train artifacts', len(tr), 'train tasks', len(set(tasks[tr])), 'test artifacts held back', len(te), 'test tasks', len(set(tasks[te])))
