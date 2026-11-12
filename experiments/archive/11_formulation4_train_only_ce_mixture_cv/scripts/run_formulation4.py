"""Formulation 4 (pick/fit the judge on ALL training tasks by loss, no validation split) on cached judge scores.
Repeated 5-fold task-grouped CV, untouched test fold. CPU only, zero model calls.
Usage: ~/.venvs/judge/bin/python run_formulation4.py --data dataset.json --out results_f4 [--repeats 20 --boot 10000]"""
import sys,json,argparse,time,platform
from pathlib import Path
import numpy as np, scipy
sys.path.insert(0,str(Path(__file__).parent/'exp10_scripts')); sys.path.insert(0,str(Path(__file__).parent/'vendor_exp03'))
from metrics import summarize
from models import histogram,smooth
from ce_mixture import fit
from historical.mixture_models import predict_mixture  # noqa
ap=argparse.ArgumentParser(); ap.add_argument('--data',required=True); ap.add_argument('--out',required=True)
ap.add_argument('--repeats',type=int,default=20); ap.add_argument('--boot',type=int,default=10000); ap.add_argument('--folds',type=int,default=5)
a=ap.parse_args(); t0=time.time(); EPS=1e-6
d=json.load(open(a.data)); rows=d['rows']; order=d['candidate_order']
p=np.array([histogram(r['ratings']) for r in rows])
q=np.stack([smooth(np.array([histogram(x) for x in d['outputs'][n]]),EPS) for n in order],axis=1)
tasks=np.array([r['task'] for r in rows]); utasks=sorted(set(tasks)); T=len(utasks)
def ce(P,Q): return -np.sum(P*np.log(Q),axis=-1)           # per artifact
def rps(P,Q):
    pc=np.cumsum(P,-1)[:,:5]; qc=np.cumsum(Q,-1)[:,:5]; return np.mean((qc-pc)**2+pc*(1-pc),axis=-1)
def tvd(P,Q): return 0.5*np.abs(P-Q).sum(-1)
METH=['constant','equal_mixture','best_single_train_ce','f4_ce_mixture']
oof={m:np.zeros((a.repeats,len(rows),6)) for m in METH}; wts=[]; best_counts=np.zeros(len(order),int); fails=0
for rep in range(a.repeats):
    rng=np.random.default_rng(20261110+rep); perm=rng.permutation(T); fold_of={utasks[t]:i%a.folds for i,t in enumerate(perm)}
    fold=np.array([fold_of[t] for t in tasks])
    for k in range(a.folds):
        tr,te=np.flatnonzero(fold!=k),np.flatnonzero(fold==k)
        marg=smooth(p[tr].mean(0),EPS); oof['constant'][rep,te]=marg
        oof['equal_mixture'][rep,te]=q[te].mean(1)
        trce=[ce(p[tr],q[tr,j]).mean() for j in range(len(order))]; b=int(np.argmin(trce)); best_counts[b]+=1
        oof['best_single_train_ce'][rep,te]=q[te,b]
        w,rec=fit(q[tr],p[tr],'ce')
        if rec['status']!='optimal': fails+=1
        wts.append(w.tolist()); oof['f4_ce_mixture'][rep,te]=np.einsum('njr,j->nr',q[te],w)
# per-artifact metric averaged over repeats, then task bootstrap
M={'ce':ce,'rps':rps,'tvd':tvd}
per={mt:{m:np.mean([f(p,oof[m][r]) for r in range(a.repeats)],axis=0) for m in METH} for mt,f in M.items()}
tidx=[np.flatnonzero(tasks==t) for t in utasks]
rng=np.random.default_rng(1110)
draws=rng.integers(0,T,size=(a.boot,T))
def tmean(x): return np.array([x[i].sum() for i in tidx]),np.array([len(i) for i in tidx])
res={'n_artifacts':len(rows),'n_tasks':T,'folds':a.folds,'repeats':a.repeats,'bootstrap_draws':a.boot,'epsilon':EPS,
     'candidate_order':order,'optimizer_certificate_failures':fails,'fits':len(wts),'metrics':{},'paired':{},
     'mean_weights':np.mean(wts,0).tolist(),'weight_sd':np.std(wts,0).tolist(),'best_single_choice_counts':dict(zip(order,best_counts.tolist())),
     'inference_calls':0,'provider_cost_usd':0,'seconds':None,
     'environment':{'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__}}
for mt in M:
    S={m:tmean(per[mt][m])[0] for m in METH}; N=tmean(per[mt][METH[0]])[1]
    res['metrics'][mt]={m:float(per[mt][m].mean()) for m in METH}
    for m in METH[:3]:
        diff=S['f4_ce_mixture']-S[m]; point=float(diff.sum()/N.sum())
        bs=np.array([diff[dr].sum()/N[dr].sum() for dr in draws]); lo,hi=np.percentile(bs,[2.5,97.5])
        res['paired'][f'{mt}: f4_ce_mixture minus {m}']={'point':point,'ci95':[float(lo),float(hi)],'tasks_where_f4_better':int((diff<0).sum()),'excludes_zero':bool(lo>0 or hi<0)}
res['seconds']=time.time()-t0
out=Path(a.out); out.mkdir(parents=True,exist_ok=False); json.dump(res,open(out/'results.json','w'),indent=1)
print(json.dumps(res,indent=1))
