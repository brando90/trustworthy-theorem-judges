"""TLDR: Compare four matched softmax-head fitting losses with one shared validation rule."""
import argparse, collections, hashlib, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize, check_grad
from scipy.special import softmax, log_softmax
from metrics import histogram, per_item, summarize, smooth
from run_cached import partitions, dump

LOSSES=('ce','brier','rps','pearson')
GRID=np.arange(6)/5

def objective(w, x, p, loss, strength):
    w=w.reshape(x.shape[1],6);q=softmax(x@w,axis=1);n=len(x)
    if loss=='ce':
        value=-np.sum(p*log_softmax(x@w,axis=1))/n;gz=(q-p)/n
    else:
        if loss=='brier':value=np.mean(1+(q*q).sum(1)-2*(p*q).sum(1));gq=2*(q-p)/n
        elif loss=='rps':
            fp=np.cumsum(p,axis=1)[:,:5];fq=np.cumsum(q,axis=1)[:,:5]
            value=np.mean(fq*fq-2*fq*fp+fp)
            gq=np.zeros_like(q);gq[:,:5]=np.cumsum((2*(fq-fp)/(5*n))[:,::-1],axis=1)[:,::-1]
        else:
            mu=q@GRID;y=p@GRID;u=mu-mu.mean();v=y-y.mean();us=u@u+1e-12;vs=v@v+1e-12
            den=np.sqrt(us*vs);rho=u@v/den;value=1-rho
            gmu=-v/den+rho*u/us;gq=gmu[:,None]*GRID
        gz=q*(gq-(q*gq).sum(1,keepdims=True))
    return float(value+strength*np.sum(w*w)/2), (x.T@gz+strength*w).ravel()

def fit(x, p, loss, strength, seed, maxiter):
    mean=x.mean(0);sd=x.std(0);sd=np.maximum(sd,1e-8)
    z=np.column_stack([np.ones(len(x)),(x-mean)/sd]);w=np.random.default_rng(seed).normal(0,.02,size=(z.shape[1],6)).ravel()
    opt=minimize(objective,w,args=(z,p,loss,strength),method='L-BFGS-B',jac=True,
                 options={'maxiter':maxiter,'maxfun':600,'ftol':1e-10,'gtol':1e-6})
    return (mean,sd,opt.x.reshape(z.shape[1],6)),{'success':bool(opt.success),'status':int(opt.status),'iterations':int(opt.nit),'function_calls':int(opt.nfev),'finite':bool(np.all(np.isfinite(opt.x)))}

def predict(model,x):
    mean,sd,w=model;return softmax(np.column_stack([np.ones(len(x)),(x-mean)/sd])@w,axis=1)

def controls():
    rng=np.random.default_rng(13);x=np.column_stack([np.ones(8),rng.normal(size=(8,2))]);p=rng.dirichlet(np.ones(6),size=8);w=rng.normal(0,.2,size=18)
    errors={}
    for loss in LOSSES:
        err=check_grad(lambda v:objective(v,x,p,loss,.01)[0],lambda v:objective(v,x,p,loss,.01)[1],w)
        errors[loss]=float(err);assert err<1e-5,(loss,err)
    x=np.array([[-1.],[1.]]);p=np.eye(6)[[0,5]]
    model,receipt=fit(x,p,'ce',0,17,300)
    loss=float(per_item(p,smooth(predict(model,x),1e-8))['ce'].mean());assert loss<.001
    return {'gradient_errors':errors,'two_example_fit_ce':loss,'status':'PASS'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--controls-only',action='store_true');a=ap.parse_args()
    control=controls()
    if a.controls_only:print(json.dumps(control));return
    root=Path(a.root);start=time.time();cfg=json.loads((root/'head_protocol.json').read_text());base=json.loads((root/'protocol.json').read_text())
    assert hashlib.sha256((root/'private/dataset.json').read_bytes()).hexdigest()==base['dataset_sha256']
    d=json.loads((root/'private/dataset.json').read_text());rows=d['rows'];n=len(rows)
    x=np.array([np.mean(d['outputs'][name],axis=1)/5 for name in base['candidate_order']]).T
    p=np.array([histogram(r['ratings']) for r in rows]);outputs={k:[] for k in LOSSES};fits=[];choices=[];models=[]
    def progress(state):state.update(elapsed_seconds=time.time()-start);dump(root/'output/head_progress.json',state);print(json.dumps(state),flush=True)
    for si,(outer,inners) in enumerate(partitions(rows,base['seeds'])):
        forecasts={k:np.empty_like(p) for k in LOSSES}
        for fold in range(5):
            tr=np.flatnonzero(outer!=fold);te=np.flatnonzero(outer==fold);inner=inners[fold]
            for loss in LOSSES:
                scores=[]
                for strength in cfg['l2_strengths']:
                    held=np.empty((len(tr),6))
                    for f in range(4):
                        train=tr[[inner[rows[i]['family']]!=f for i in tr]]
                        valid_local=np.flatnonzero([inner[rows[i]['family']]==f for i in tr]);valid=tr[valid_local]
                        assert not ({rows[i]['family'] for i in train}&{rows[i]['family'] for i in valid})
                        model,rec=fit(x[train],p[train],loss,strength,base['seeds'][si]+100*fold+f,cfg['maxiter'])
                        fits.append({'seed':base['seeds'][si],'outer_fold':fold,'inner_fold':f,'loss':loss,'l2':strength,**rec})
                        assert rec['finite'];held[valid_local]=smooth(predict(model,x[valid]),cfg['epsilon'])
                    scores.append(float(per_item(p[tr],held)['rps'].mean()))
                chosen=min(range(len(scores)),key=lambda i:(scores[i],i));strength=cfg['l2_strengths'][chosen]
                model,rec=fit(x[tr],p[tr],loss,strength,base['seeds'][si]+100*fold+99,cfg['maxiter'])
                assert rec['finite'];fits.append({'seed':base['seeds'][si],'outer_fold':fold,'inner_fold':None,'loss':loss,'l2':strength,**rec})
                forecasts[loss][te]=smooth(predict(model,x[te]),cfg['epsilon'])
                choices.append({'seed':base['seeds'][si],'outer_fold':fold,'loss':loss,'l2':strength,'inner_rps':scores})
                models.append({'loss':loss,'seed':base['seeds'][si],'fold':fold,'mean':model[0],'sd':model[1],'weights':model[2]})
            progress({'phase':'fitting','completed_outer_folds':si*5+fold+1,'fits':len(fits)})
        for loss in LOSSES:outputs[loss].append(forecasts[loss])
    itemmetrics={k:[per_item(p,q) for q in qs] for k,qs in outputs.items()}
    def aggregate(ix):
        ans={}
        for k,ms in itemmetrics.items():
            vs=[summarize(m,ix) for m in ms];ans[k]={m:float(np.mean([v[m] for v in vs])) for m in vs[0]}
        return ans
    matrix=aggregate(np.arange(n));families=np.array([r['family'] for r in rows]);fam=sorted(set(families))
    rng=np.random.default_rng(base['bootstrap_seed']);samples={k:{m:[] for m in matrix[k]} for k in LOSSES};diffs={m:[] for m in matrix['ce']}
    for b in range(cfg['bootstrap_draws']):
        draw=rng.choice(fam,size=len(fam),replace=True);ix=np.concatenate([np.flatnonzero(families==g) for g in draw]);v=aggregate(ix)
        for k in LOSSES:
            for m in v[k]:samples[k][m].append(v[k][m])
        for m in diffs:diffs[m].append(v['ce'][m]-v['pearson'][m])
        if (b+1)%200==0:progress({'phase':'bootstrap','completed':b+1})
    def ci(v):
        v=np.asarray(v);v=v[np.isfinite(v)]
        return {'lo':float(np.quantile(v,.025)),'hi':float(np.quantile(v,.975)),'valid_draws':len(v)}
    result={'matrix':matrix,'conditional_intervals':{k:{m:ci(v) for m,v in ms.items()} for k,ms in samples.items()},
            'ce_minus_pearson':{m:{'estimate':matrix['ce'][m]-matrix['pearson'][m],**ci(v)} for m,v in diffs.items()},
            'per_seed':{k:[summarize(m,np.arange(n)) for m in ms] for k,ms in itemmetrics.items()},
            'controls':control,'fit_count':len(fits),'nonconverged_fits':sum(not f['success'] for f in fits),
            'fits':fits,'choices':choices,'elapsed_seconds':time.time()-start,'bootstrap_draws':cfg['bootstrap_draws'],
            'head_protocol_sha256':hashlib.sha256((root/'head_protocol.json').read_bytes()).hexdigest(),
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'dataset_sha256':base['dataset_sha256'],'new_inference_calls':0,'provider_cost_usd':0}
    assert len(fits)==900 and len(choices)==100
    dump(root/'private/run/head_forecasts.json',{'outputs':outputs,'models':models,'bootstrap_differences':diffs})
    dump(root/'output/head_results.json',result);progress({'phase':'complete','status':'COMPLETE','fits':len(fits)})

if __name__=='__main__':main()
