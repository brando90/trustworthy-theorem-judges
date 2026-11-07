"""TLDR: Execute frozen historical objective selection and paired family resampling."""
import argparse, collections, hashlib, json, platform, time, warnings
from pathlib import Path
import numpy as np
import scipy
from metrics import OBJECTIVES, histogram, smooth, per_item, summarize, choose, pearson
from scipy.stats import rankdata

def dump(path, data):
    def clean(x):
        if isinstance(x,dict):return {str(k):clean(v) for k,v in x.items()}
        if isinstance(x,(list,tuple)):return [clean(v) for v in x]
        if isinstance(x,np.ndarray):return clean(x.tolist())
        if isinstance(x,(float,np.floating)):return float(x) if np.isfinite(x) else None
        if isinstance(x,np.integer):return int(x)
        return x
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(clean(data),sort_keys=True,indent=2,allow_nan=False)+'\n')

def partitions(rows, seeds):
    families=sorted({r['family'] for r in rows}); result=[]
    for seed in seeds:
        order=np.random.default_rng(seed).permutation(families)
        byfamily={g:i%5 for i,g in enumerate(order)}
        outer=np.array([byfamily[r['family']] for r in rows])
        inner=[]
        for fold in range(5):
            remaining=[g for g in order if byfamily[g]!=fold]
            inner.append({g:i%4 for i,g in enumerate(remaining)})
        result.append((outer,inner))
    return result

def evaluate(rows, rawq, p, cfg, epsilon, bootstrap=False, progress=None):
    n=len(rows); names=cfg['candidate_order']; seeds=cfg['seeds']
    assert set(collections.Counter(r['task'] for r in rows).values())=={3}
    parts=partitions(rows,seeds)
    q=np.array([smooth(rawq[name],epsilon) for name in names])
    items=[per_item(p,qq) for qq in q]
    selections=[]; predictions={o:[] for o in OBJECTIVES}; fallbacks=0
    for si,(outer,inner) in enumerate(parts):
        selected={o:np.empty_like(p) for o in OBJECTIVES}
        for fold in range(5):
            train=np.flatnonzero(outer!=fold); test=np.flatnonzero(outer==fold)
            assert not ({rows[i]['family'] for i in train}&{rows[i]['family'] for i in test})
            assert all(rows[i]['family'] in inner[fold] for i in train)
            # Fixed predictions have no fitted parameters. Pool the four inner held-out sets.
            score=[summarize(m,train) for m in items]
            ce_j,_=choose(score,'ce',names); kl_j,_=choose(score,'kl',names)
            assert ce_j==kl_j
            for objective in OBJECTIVES:
                j,fallback=choose(score,objective,names);fallbacks+=fallback
                selected[objective][test]=q[j,test]
                selections.append({'seed':seeds[si],'fold':fold,'objective':objective,'candidate':names[j],
                                   'validation_artifacts':len(train),'test_artifacts':len(test),'undefined_fallback':fallback})
        for o in OBJECTIVES:predictions[o].append(per_item(p,selected[o]))
        if progress:progress({'phase':'outer_folds','epsilon':epsilon,'seed_completed':seeds[si]})
    metric_names=list(summarize(items[0],np.arange(n)))
    def aggregate(index):
        out={}
        for o in OBJECTIVES:
            values=[summarize(m,index) for m in predictions[o]]
            out[o]={k:float(np.mean([v[k] for v in values])) for k in metric_names}
        return out
    summary=aggregate(np.arange(n))
    result={'artifacts':n,'tasks':len({r['task'] for r in rows}),'families':len({r['family'] for r in rows}),
            'expert_ratings':sum(len(r['ratings']) for r in rows),'epsilon':epsilon,'matrix':summary,
            'selections':selections,'undefined_selection_fallbacks':fallbacks,
            'per_seed':{o:[summarize(m,np.arange(n)) for m in predictions[o]] for o in OBJECTIVES},
            'fixed_candidate_descriptive':{name:summarize(m,np.arange(n)) for name,m in zip(names,items)},
            'zero_mass_before_smoothing':{name:{'artifacts':int(np.any((p>0)&(rawq[name]==0),axis=1).sum()),
              'mean_human_mass':float((p*(rawq[name]==0)).sum(1).mean())} for name in names}}
    if not bootstrap:return result,None
    fam=sorted({r['family'] for r in rows}); families=np.array([r['family'] for r in rows])
    rng=np.random.default_rng(cfg['bootstrap_seed']); B=cfg['bootstrap_draws']
    conditional={o:{k:[] for k in metric_names} for o in OBJECTIVES}
    conditional_delta={k:[] for k in metric_names}; redo_delta=[]; ledger=[]
    for b in range(B):
        draw=rng.choice(fam,size=len(fam),replace=True)
        idx=np.concatenate([np.flatnonzero(families==g) for g in draw])
        a=aggregate(idx)
        for o in OBJECTIVES:
            for k in metric_names:conditional[o][k].append(a[o][k])
        for k in metric_names:conditional_delta[k].append(a['ce'][k]-a['spearman'][k])
        diffs=[]; invalid=False
        for outer,_ in parts:
            total=0.;count=0
            for fold in range(5):
                tr=idx[outer[idx]!=fold];te=idx[outer[idx]==fold]
                if not len(te):continue
                if len(tr)==0:invalid=True;break
                ces=[float(m['ce'][tr].mean()) for m in items]
                hrank=rankdata(items[0]['human_mean'][tr])
                sps=[pearson(rankdata(m['judge_mean'][tr]),hrank) for m in items]
                jc=int(np.argmin(ces))
                js,_=choose([{'spearman':v} for v in sps],'spearman',names)
                total+=float((items[jc]['ce'][te]-items[js]['ce'][te]).sum());count+=len(te)
            if invalid:break
            diffs.append(total/count)
        redo_delta.append(float(np.mean(diffs)) if not invalid else float('nan'))
        ledger.append({'draw':b,'unique_families':len(set(draw)),'valid':not invalid})
        if progress and (b+1)%50==0:progress({'phase':'bootstrap','completed':b+1,'total':B})
    def interval(v):
        v=np.asarray(v);v=v[np.isfinite(v)]
        return {'lo':float(np.quantile(v,.025)) if len(v) else None,
                'hi':float(np.quantile(v,.975)) if len(v) else None,'valid_draws':len(v)}
    result['conditional_intervals']={o:{k:interval(v) for k,v in d.items()} for o,d in conditional.items()}
    result['ce_minus_spearman']={k:{'estimate':summary['ce'][k]-summary['spearman'][k],**interval(v)} for k,v in conditional_delta.items()}
    result['primary_selection_refit_interval']={'estimate':summary['ce']['ce']-summary['spearman']['ce'],**interval(redo_delta)}
    result['bootstrap_draws']=B
    private={'conditional':conditional,'paired_differences':conditional_delta,'selection_refit':redo_delta,'ledger':ledger,
             'partitions':[{'outer':o.tolist(),'inner':i} for o,i in parts]}
    return result,private

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--data',required=True);ap.add_argument('--config',required=True)
    ap.add_argument('--out',required=True);ap.add_argument('--private-out',required=True);a=ap.parse_args()
    out=Path(a.out);private=Path(a.private_out);assert not (out/'results.json').exists()
    start=time.time();cfg=json.loads(Path(a.config).read_text());data=json.loads(Path(a.data).read_text())
    assert hashlib.sha256(Path(a.data).read_bytes()).hexdigest()==cfg['dataset_sha256']
    def progress(state):
        state.update(elapsed_seconds=time.time()-start);dump(out/'progress.json',state);print(json.dumps(state),flush=True)
    rows=data['rows'];p=np.array([histogram(r['ratings']) for r in rows])
    rawq={name:np.array([histogram(v) for v in data['outputs'][name]]) for name in cfg['candidate_order']}
    warnings.filterwarnings('ignore',message='An input array is constant')
    primary,private_result=evaluate(rows,rawq,p,cfg,1e-6,True,progress)
    dump(private/'bootstrap.json',private_result)
    sensitivities={}
    for eps in [1e-8,1e-4]:sensitivities[str(eps)]=evaluate(rows,rawq,p,cfg,eps,False,progress)[0]
    for label,condition in [('ordinary',lambda r:r['ordinary']),('ordinary_unambiguous',lambda r:r['ordinary'] and not r['ambiguous'])]:
        ix=np.array([i for i,r in enumerate(rows) if condition(r)])
        sensitivities[label]=evaluate([rows[i] for i in ix],{n:q[ix] for n,q in rawq.items()},p[ix],cfg,1e-6,False,progress)[0]
    # Original split: select on historical validation only and score old test only.
    val=np.array([i for i,r in enumerate(rows) if r['split']=='val']);test=np.array([i for i,r in enumerate(rows) if r['split']=='test'])
    assert len(val)==15 and len(test)==30
    ms=[per_item(p,smooth(rawq[name],1e-6)) for name in cfg['candidate_order']]
    vs=[summarize(m,val) for m in ms]
    original={}
    for o in OBJECTIVES:
        j,f=choose(vs,o,cfg['candidate_order']);original[o]={'candidate':cfg['candidate_order'][j],'metrics':summarize(ms[j],test),'fallback':f}
    repeat={name:{'raw_repeat_rms_sample_sd_0_1':float(np.sqrt(np.mean(np.var(np.array(data['outputs'][name])/5,axis=1,ddof=1)))),
                  'repeats_per_artifact':3} for name in cfg['candidate_order']}
    human=[]
    for expert in range(3):
        xx=[];yy=[]
        for r in rows:
            v=r['ratings_by_expert'];other=[x for j,x in enumerate(v) if j!=expert and x is not None]
            if v[expert] is not None and other:xx.append(v[expert]/5);yy.append(np.mean(other)/5)
        from metrics import correlations
        human.append({'expert_index':expert+1,'artifacts':len(xx),**correlations(xx,yy),'mae':float(np.mean(np.abs(np.array(xx)-yy)))})
    # Train-only constant PMF reference in each outer fold; not a pool member.
    baselines=[]
    for outer,_ in partitions(rows,cfg['seeds']):
        q=np.empty_like(p)
        for fold in range(5):q[outer==fold]=smooth(p[outer!=fold].mean(0),1e-6)
        baselines.append(summarize(per_item(p,q),np.arange(len(rows))))
    result={'primary':primary,'sensitivities':sensitivities,'original_split':original,'repeat_variability':repeat,
            'human_leave_one_expert_out_descriptive':human,'training_marginal_baseline_per_seed':baselines,
            'elapsed_seconds':time.time()-start,'new_inference_calls':0,'provider_cost_usd':0,
            'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,
            'config_sha256':hashlib.sha256(Path(a.config).read_bytes()).hexdigest(),'dataset_sha256':cfg['dataset_sha256']}
    dump(out/'results.json',result);progress({'phase':'complete','status':'COMPLETE'})

if __name__=='__main__':main()
