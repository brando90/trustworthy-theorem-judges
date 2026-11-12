"""Rebuild the 75-artifact cached dataset (human expert ratings + 5 judges x 3 cached repeats) from veribench exp 100 (commit be287d9)."""
import json,glob,collections
base='/var/lib/agent/scratch/AT-2807/veribench/experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test'
rows=[json.loads(l) for l in open(base+'/inputs/items.jsonl')]
split={r['item']:r['split'] for r in rows}
RUNS={'H0_sol':['w1_H0_sol_high','ab_H0_sol'],'H0_opus':['w1_H0_opus55_max','ab_H0_opus'],
 'H1_sol':['p3_i1_H1_sol_high','ab_H1_sol'],'H2_sol':['p3_i2_H2_sol_high','p4_val_H2_sol_high','p5_test_H2_sol_high'],
 'H2_opus':['p3_i3_H2_opus55_max','p4_val_H2_opus55_max','p5_test_H2_opus55_max']}
# a run supplies an item only for the split(s) it was built for; train run -> train items, others -> val/test items
out={}
for name,runs in RUNS.items():
    got=collections.defaultdict(dict)
    for ri,run in enumerate(runs):
        for f in sorted(glob.glob(f'{base}/runs/{run}/receipts/*.json')):
            d=json.load(open(f))
            if d.get('status')!='COMPLETE' or d.get('kind')!='main' or d['item'] not in split: continue
            want='train' if ri==0 else None
            sp=split[d['item']]
            if ri==0 and sp!='train': continue
            if ri>0 and sp=='train': continue
            if ri>0 and run.startswith('p4_') and sp!='val': continue
            if ri>0 and run.startswith('p5_') and sp!='test': continue
            got[d['item']][d['repeat']]=int(d['score_raw'])
    out[name]=got
    print(name,len(got),collections.Counter(len(v) for v in got.values()))
data={'source_commit':'be287d9bb2f7bd35ba6db1b8735c9ba10d00eade','candidate_order':list(RUNS),
 'rows':[{'item':r['item'],'task':r['task'],'split':r['split'],'domain':r['domain'],
          'ratings':[int(r[k]) for k in ('p1','p2','p3') if r.get(k) is not None]} for r in rows],
 'outputs':{n:[[out[n][r['item']][k] for k in (1,2,3)] for r in rows] for n in RUNS}}
json.dump(data,open('dataset.json','w'))
print('rows',len(rows),'ratings',sum(len(r['ratings']) for r in data['rows']))
