"""Execute the hash-bound retrospective study; no model or network calls."""
import argparse
from collections import Counter
import gzip
import hashlib
import json
import platform
from pathlib import Path
import time

import numpy as np
import scipy

from metrics import summarize, interval
from models import histogram, smooth, train_select, predict

ROOT=Path(__file__).resolve().parents[1]


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def dump(path, obj):
    path=Path(path); path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,indent=2,allow_nan=False,sort_keys=True)+'\n')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--data',required=True)
    ap.add_argument('--out',required=True)
    ap.add_argument('--private-out',required=True)
    args=ap.parse_args()
    cfg=json.loads((ROOT/'protocol.json').read_text())
    freeze=json.loads((ROOT/'FREEZE.json').read_text())
    required={'protocol.json','PROTOCOL.md'} | {str(p.relative_to(ROOT)) for p in (ROOT/'scripts').rglob('*.py')}
    assert required <= set(freeze['files'])
    for name, sha in freeze['files'].items():
        assert digest(ROOT/name)==sha, name
    assert digest(args.data)==cfg['dataset_sha256']
    out, private=Path(args.out),Path(args.private_out)
    assert not out.exists() and not private.exists(), 'Use new output directories.'
    out.mkdir(parents=True); private.mkdir(parents=True)
    start=time.monotonic()
    d=json.loads(Path(args.data).read_text()); rows=d['rows']
    assert d['source_commit']=='be287d9bb2f7bd35ba6db1b8735c9ba10d00eade'
    p=np.array([histogram(r['ratings']) for r in rows])
    q=np.stack([smooth(np.array([histogram(a) for a in d['outputs'][name]]),cfg['epsilon'])
                for name in cfg['candidate_order']],axis=1)
    assert len(rows)==75 and q.shape==(75,5,6)
    assert sum(len(r['ratings']) for r in rows)==195
    assert all(len(v)==3 for name in cfg['candidate_order'] for v in d['outputs'][name])
    split=np.array([r['split'] for r in rows]); family=np.array([r['family'] for r in rows])
    ix={s:np.flatnonzero(split==s) for s in cfg['split_labels']}
    assert [len(ix[s]) for s in cfg['split_labels']]==[30,15,30]
    assert not any({rows[i]['task'] for i in ix[a]} & {rows[i]['task'] for i in ix[b]}
                   for a,b in [('train','val'),('train','test'),('val','test')])
    models, fits, selection=train_select(q[ix['train']],p[ix['train']],q[ix['val']],p[ix['val']],cfg)
    dump(out/'fit_receipts.json',fits)
    if models is None:
        dump(out/'FAILED.json',selection)
        raise RuntimeError('Primary fits failed; no test evaluation.')
    # Save selected parameters before any test metric is computed.
    dump(out/'selected_models.json',{'models':models,'selection':selection,
         'candidate_order':cfg['candidate_order'],'epsilon':cfg['epsilon'],
         'dataset_sha256':cfg['dataset_sha256'],'freeze_sha256':digest(ROOT/'FREEZE.json')})
    selected_hash=digest(out/'selected_models.json')
    qs={method:predict(q,model) for method,model in models.items()}
    for j,name in enumerate(cfg['candidate_order']): qs['cached_'+name]=q[:,j]
    matrix={s:{method:summarize(p[index],forecast[index]) for method,forecast in qs.items()}
            for s,index in ix.items()}
    # Per-artifact ratings/forecasts and the source-row trace remain private.
    dump(research_artifacts/'forecasts.json',{'row_order':[r['item'] for r in rows],
                                  'predictions':{k:v.tolist() for k,v in qs.items()}})
    first=int(ix['train'][0])
    dump(research_artifacts/'training_trace.json',{'source_row_index':first,'row':rows[first],
         'cached_repeat_ratings':{n:d['outputs'][n][first] for n in cfg['candidate_order']},
         'histograms':q[first].tolist(),'human_histogram':p[first].tolist(),
         'predictions':{k:v[first].tolist() for k,v in qs.items()},
         'dataset_sha256':cfg['dataset_sha256']})
    test_metrics=list(matrix['test']['method4_rps'])
    refits={method:{m:[] for m in test_metrics} for method in models}
    fixed={method:{m:[] for m in test_metrics} for method in models}
    deltas={m:[] for m in test_metrics}; fixed_deltas={m:[] for m in test_metrics}
    families=sorted(set(family)); rng=np.random.default_rng(cfg['bootstrap_seed'])
    ledger=[]; receipts=[]; selected_counts=Counter(); shrinkage_counts={m:Counter() for m in ['method2_pearson','method4_rps']}
    for draw in range(cfg['bootstrap_draws']):
        sampled=rng.choice(families,size=len(families),replace=True)
        ids=np.concatenate([np.flatnonzero(family==f) for f in sampled])
        bi={s:ids[split[ids]==s] for s in ix}
        valid=len(bi['train'])>=2 and len(bi['val'])>0 and len(bi['test'])>0
        reason=None; bm=None
        if valid:
            bm,bf,bs=train_select(q[bi['train']],p[bi['train']],q[bi['val']],p[bi['val']],cfg)
            for f in bf: receipts.append(dict(f,draw=draw))
            valid=bm is not None
            if not valid: reason='fit_certificate_failed'
        else: reason='empty_or_insufficient_split'
        ledger.append({'draw':draw,'valid':valid,'reason':reason,
                       'counts':{s:len(v) for s,v in bi.items()},'unique_families':len(set(sampled))})
        if valid:
            selected_counts[bs['practical_selected_method']]+=1
            for method in shrinkage_counts: shrinkage_counts[method][str(bm[method]['shrinkage'])]+=1
            metrics={m:summarize(p[bi['test']],predict(q[bi['test']],model)) for m,model in bm.items()}
            fm={m:summarize(p[bi['test']],qs[m][bi['test']]) for m in bm}
            for method in refits:
                for metric in test_metrics:
                    refits[method][metric].append(metrics[method][metric])
                    fixed[method][metric].append(fm[method][metric])
            for metric in test_metrics:
                a,b=metrics['method4_rps'][metric],metrics['method2_pearson'][metric]
                deltas[metric].append(None if a is None or b is None else a-b)
                a,b=fm['method4_rps'][metric],fm['method2_pearson'][metric]
                fixed_deltas[metric].append(None if a is None or b is None else a-b)
        else:
            for method in refits:
                for metric in test_metrics:
                    refits[method][metric].append(None); fixed[method][metric].append(None)
            for metric in test_metrics: deltas[metric].append(None); fixed_deltas[metric].append(None)
        if (draw+1)%100==0:
            elapsed=time.monotonic()-start
            progress={'draws_completed':draw+1,'draws_requested':cfg['bootstrap_draws'],
                      'elapsed_seconds':elapsed,'failed_draws':sum(not l['valid'] for l in ledger)}
            dump(out/'progress.json',progress); print(json.dumps(progress),flush=True)
            if elapsed>cfg['max_wall_seconds']:
                dump(out/'bootstrap_ledger.json',ledger)
                raise TimeoutError('Fixed wall budget exceeded; partial records retained.')
    counts={s:{'artifacts':len(index),'tasks':len({rows[i]['task'] for i in index}),
               'families':len(set(family[index])),
               'ratings':sum(len(rows[i]['ratings']) for i in index)} for s,index in ix.items()}
    counts['total']={'artifacts':len(rows),'tasks':len({r['task'] for r in rows}),
                     'families':len(families),'ratings':sum(len(r['ratings']) for r in rows)}
    repeats={name:{'repeats_per_artifact':3,'rms_within_artifact_sample_sd_normalized':
                   float(np.sqrt(np.mean(np.var(np.asarray(d['outputs'][name])/5,axis=1,ddof=1))))}
              for name in cfg['candidate_order']}
    comparison={m:{'estimate':None if matrix['test']['method4_rps'][m] is None or matrix['test']['method2_pearson'][m] is None
                   else matrix['test']['method4_rps'][m]-matrix['test']['method2_pearson'][m],**interval(v)} for m,v in deltas.items()}
    result={'status':'complete_retrospective_only','counts':counts,'metrics':matrix,
        'paired_method4_minus_method2':comparison,
        'refit_intervals':{method:{m:interval(v) for m,v in mm.items()} for method,mm in refits.items()},
        'fixed_prediction_intervals':{method:{m:interval(v) for m,v in mm.items()} for method,mm in fixed.items()},
        'paired_fixed_intervals':{m:interval(v) for m,v in fixed_deltas.items()},
        'selection':selection,'bootstrap_selection_counts':dict(selected_counts),
        'bootstrap_shrinkage_counts':{m:dict(c) for m,c in shrinkage_counts.items()},
        'repeat_variability':repeats,'models':d['models'],'source_commit':d['source_commit'],
        'primary_fit_requests':len(fits),'primary_objective_fits':sum(f['objective']!='shared_constant' for f in fits),
        'bootstrap_fit_requests':len(receipts),'bootstrap_valid_draws':sum(l['valid'] for l in ledger),
        'bootstrap_draws':cfg['bootstrap_draws'],'elapsed_seconds':time.monotonic()-start,
        'environment':{'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__},
        'dataset_sha256':cfg['dataset_sha256'],'freeze_sha256':digest(ROOT/'FREEZE.json'),
        'selected_models_before_test_sha256':selected_hash,
        'private_forecasts_sha256':digest(research_artifacts/'forecasts.json'),
        'trace_sha256':digest(research_artifacts/'training_trace.json'),
        'literal_compliance':'No prompt or raw semantic judge was changed; the cache supplies scalar ratings only.',
        'inference_calls':0,'provider_cost_usd':0}
    dump(out/'bootstrap_ledger.json',ledger)
    with gzip.open(out/'bootstrap_fit_receipts.json.gz','wt') as f:
        json.dump(receipts,f,allow_nan=False,sort_keys=True)
    dump(research_artifacts/'bootstrap_distributions.json',{'refit':refits,'fixed':fixed,'paired':deltas})
    dump(out/'results.json',result)
    print(json.dumps({'status':result['status'],'primary':comparison['rps'],'elapsed_seconds':result['elapsed_seconds']},indent=2))


if __name__=='__main__': main()
