"""Merge the 3 new frontier judges (3 calls per artifact, raw_<judge>/<item>__r<k>.json) into the experiment-12 dataset (5 cached judges).
Writes dataset_new3.json (new judges only) and dataset_all8.json (5 cached + 3 new); dataset_old5.json is the cached-only baseline.
usage: build_pool.py --raw DIR_WITH_raw_* --old dataset_old5.json --out DIR"""
import argparse, json, glob, os
ap=argparse.ArgumentParser(); ap.add_argument('--raw',required=True); ap.add_argument('--old',required=True); ap.add_argument('--out',required=True); a=ap.parse_args()
d=json.load(open(a.old)); NEW={'astra':'H2_astra','sol61':'H2_sol61','argon':'H2_argon'}
new={}
for j,name in NEW.items():
    outs=[]
    for r in d['rows']:
        sc=[]
        for k in (1,2,3):
            f=f'{a.raw}/raw_{j}/{r["item"]}__r{k}.json'; x=json.load(open(f))
            assert x['status']=='COMPLETE',(f,x['status']); sc.append(int(x['score_raw']))
        outs.append(sc)
    new[name]=outs
os.makedirs(a.out,exist_ok=True)
def dump(order,fn,src):
    e=dict(d); e['candidate_order']=order; e['outputs']={n:src[n] for n in order}; json.dump(e,open(f'{a.out}/{fn}','w'))
allo=dict(d['outputs']); allo.update(new)
dump(list(new),'dataset_new3.json',allo); dump(list(d['candidate_order'])+list(new),'dataset_all8.json',allo)
print({n:[round(sum(s)/3,2) for s in v][:5] for n,v in new.items()})
