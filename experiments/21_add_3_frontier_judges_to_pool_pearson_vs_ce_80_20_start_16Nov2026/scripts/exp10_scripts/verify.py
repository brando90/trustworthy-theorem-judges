"""Independent scalar reconstruction of frozen-model probabilities and test metrics."""
import argparse
import hashlib
import json
from pathlib import Path
import math

import numpy as np
from scipy.stats import pearsonr, spearmanr, kendalltau


def hist(rs):
    return [rs.count(k)/len(rs) for k in range(6)]


def floor(p,eps):
    a=[max(v,eps) for v in p]; s=sum(a)
    return [v/s for v in a]


def expected_metrics(rows,probs):
    names=['rps','ce','tvd','brier','kl','weighted_pmf','empirical_cdf_squared_distance',
           'empirical_disagreement','entropy','mse','mae','bias','judge_mean','human_mean']
    accum={k:[] for k in names}
    for row,q in zip(rows,probs):
        ratings=row['ratings']; p=hist(ratings)
        pc=[sum(p[:k+1]) for k in range(5)]; qc=[sum(q[:k+1]) for k in range(5)]
        ent=-sum(v*math.log(v) for v in p if v>0)
        ce=sum(-math.log(q[r]) for r in ratings)/len(ratings)
        jm=sum(k*q[k]/5 for k in range(6)); hm=sum(ratings)/len(ratings)/5
        rs=sum(sum((qc[k]-(1 if r<=k else 0))**2 for k in range(5))/5 for r in ratings)/len(ratings)
        bs=sum(sum((q[k]-(1 if r==k else 0))**2 for k in range(6)) for r in ratings)/len(ratings)
        values=[rs,ce,sum(abs(p[k]-q[k]) for k in range(6))/2,bs,ce-ent,
                sum(p[k]*(p[k]-q[k])**2 for k in range(6)),
                sum((pc[k]-qc[k])**2 for k in range(5))/5,
                sum(pc[k]*(1-pc[k]) for k in range(5))/5,ent,
                (jm-hm)**2,abs(jm-hm),jm-hm,jm,hm]
        for k,v in zip(names,values): accum[k].append(v)
    out={k:sum(v)/len(v) for k,v in accum.items()}
    x,y=accum['judge_mean'],accum['human_mean']
    out.update(nrmse=math.sqrt(out['mse']),root_mean_cdf_distance=math.sqrt(out['empirical_cdf_squared_distance']),
               judge_sd=float(np.std(x)),human_sd=float(np.std(y)))
    if np.std(x)*math.sqrt(len(x))<=1e-12 or np.std(y)*math.sqrt(len(y))<=1e-12:
        out.update(pearson=None,spearman=None,kendall_tau_b=None)
    else:
        out.update(pearson=float(pearsonr(x,y).statistic),spearman=float(spearmanr(x,y).statistic),
                   kendall_tau_b=float(kendalltau(x,y).statistic))
    return out


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--data',required=True);ap.add_argument('--results',required=True)
    ap.add_argument('--private-results',required=True);args=ap.parse_args()
    root=Path(args.results);private=Path(args.private_results)
    d=json.loads(Path(args.data).read_text());result=json.loads((root/'results.json').read_text())
    selected=json.loads((root/'selected_models.json').read_text()); forecasts=json.loads((research_artifacts/'forecasts.json').read_text())
    assert hashlib.sha256(Path(args.data).read_bytes()).hexdigest()==result['dataset_sha256']
    assert hashlib.sha256((root/'selected_models.json').read_bytes()).hexdigest()==result['selected_models_before_test_sha256']
    order=selected['candidate_order'];eps=selected['epsilon'];max_qerr=0.;max_metric=0.;nmetrics=0
    for method,model in selected['models'].items():
        reconstructed=[]
        for i in range(len(d['rows'])):
            if model['kind']=='constant': prob=model['constant']
            else:
                base=[floor(hist(d['outputs'][name][i]),eps) for name in order]
                prob=[(1-model['shrinkage'])*sum(model['weights'][j]*base[j][k] for j in range(5))+
                      model['shrinkage']*model['constant'][k] for k in range(6)]
            reconstructed.append(prob)
        err=float(np.max(np.abs(np.array(reconstructed)-forecasts['predictions'][method])))
        max_qerr=max(max_qerr,err)
        assert err<1e-12
    for split,all_methods in result['metrics'].items():
        ix=[i for i,r in enumerate(d['rows']) if r['split']==split]
        for method,reported in all_methods.items():
            independent=expected_metrics([d['rows'][i] for i in ix],[forecasts['predictions'][method][i] for i in ix])
            for metric,value in independent.items():
                if value is None: assert reported[metric] is None
                else:
                    err=abs(value-reported[metric]);max_metric=max(max_metric,err)
                    assert err<1e-10,(split,method,metric,err)
                nmetrics+=1
    boot=json.loads((research_artifacts/'bootstrap_distributions.json').read_text());max_cierr=0.
    for metric,values in boot['paired'].items():
        a=[v for v in values if v is not None]
        rep=result['paired_method4_minus_method2'][metric]
        assert len(a)==rep['valid_draws']
        if a:
            lo,hi=np.quantile(a,[.025,.975])
            err=max(abs(lo-rep['low']),abs(hi-rep['high']));max_cierr=max(max_cierr,float(err))
            assert err<1e-12
    record={'status':'passed','independent_fitted_forecasts':len(selected['models'])*len(d['rows']),
            'independent_metric_entries':nmetrics,'max_probability_error':max_qerr,
            'max_metric_error':max_metric,'max_paired_interval_error':max_cierr,
            'scope':'Independent scalar forecasts/metrics and saved paired interval endpoints; bootstrap fits not independently rerun.',
            'source_dataset_sha256':result['dataset_sha256']}
    (root/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))


if __name__=='__main__':main()
