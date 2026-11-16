"""Experiment 21 extras (no model calls): (a) single-judge scores vs human ratings on all 75 artifacts, (b) pool effect: 8-judge pool minus cached 5-judge pool on the same 1,000 splits,
(c) fixed-split agent bootstrap over the 5 test tasks. Usage: extras21.py --pools DIR_with_dataset_all8 --results DIR --out FILE"""
import argparse, json
import numpy as np
from common import *
ap=argparse.ArgumentParser(); ap.add_argument('--all8',required=True); ap.add_argument('--results',required=True); ap.add_argument('--out',required=True); a=ap.parse_args()
d,rows,order,p,q,tasks=load(a.all8); hm=p@GRID; out={'judge_vs_human_all75':{}}
for j,n in enumerate(order):
    s=np.array(d['outputs'][n],float).mean(1)/5
    out['judge_vs_human_all75'][n]={'pearson':pearson(s,hm),'spearman':spearman(s,hm),'mean_abs_error_0_1':float(np.mean(np.abs(s-hm))),'mean_rps_single':float(rps(p,q[:,j]).mean()),'mean_ce_single':float(ce(p,q[:,j]).mean())}
ut=sorted(set(tasks)); tidx=np.array([ut.index(t) for t in tasks]); T=len(ut)
rng=np.random.default_rng(1210); draws=rng.integers(0,T,size=(10000,T))
A=json.load(open(f'{a.results}/all8/per_artifact.json'))['per_artifact']; B=json.load(open(f'{a.results}/old5/per_artifact.json'))['per_artifact']
def boot(diff):
    st=np.bincount(tidx,weights=diff,minlength=T); n=np.bincount(tidx,minlength=T).astype(float)
    bs=np.array([st[x].sum()/n[x].sum() for x in draws]); lo,hi=np.percentile(bs,[2.5,97.5]); return {'point':float(st.sum()/n.sum()),'ci95':[float(lo),float(hi)]}
out['pool_effect_all8_minus_old5']={}
for mt in ('rps','ce','tvd'):
    for m in ('corr_mixture_pearson','ce_mixture','equal_mixture'):
        out['pool_effect_all8_minus_old5'][f'{mt}: {m}']=boot(np.array(A[mt][m])-np.array(B[mt][m]))
# fixed split, agents (Astra) on the 5 test tasks
tr,te=split_tasks(tasks,FIXED_SEED); Fx=json.load(open(f'{a.results}/fixed_split_agents_all8.json'))
tt=sorted(set(tasks[te])); out['fixed_split_agents']={'test_tasks':tt}
marg=smooth(p[tr].mean(0),EPS); per={}
for nm in ('corr','ce'):
    w=Fx['agents'][nm]['weights']; Q=sum(w[n]*q[te][:,j] for j,n in enumerate(order))+w['train_marginal']*marg; Q=smooth(Q/Q.sum(1,keepdims=True),0)
    per[nm]=score(p[te],Q)
ti=np.array([tt.index(t) for t in tasks[te]]); dr=rng.integers(0,len(tt),size=(10000,len(tt)))
for mt in ('rps','ce','tvd'):
    diff=per['corr'][mt]-per['ce'][mt]; st=np.bincount(ti,weights=diff,minlength=len(tt)); n=np.bincount(ti,minlength=len(tt)).astype(float)
    bs=np.array([st[x].sum()/n[x].sum() for x in dr]); lo,hi=np.percentile(bs,[2.5,97.5])
    out['fixed_split_agents'][f'{mt}: agent2 minus agent4']={'point':float(st.sum()/n.sum()),'ci95':[float(lo),float(hi)]}
json.dump(out,open(a.out,'w'),indent=1)
for n,v in out['judge_vs_human_all75'].items(): print(n,{k:round(x,3) for k,x in v.items()})
for k,v in out['pool_effect_all8_minus_old5'].items(): print(k,round(v['point'],4),[round(x,4) for x in v['ci95']])
for k,v in out['fixed_split_agents'].items():
    if k!='test_tasks': print(k,round(v['point'],4),[round(x,4) for x in v['ci95']])
