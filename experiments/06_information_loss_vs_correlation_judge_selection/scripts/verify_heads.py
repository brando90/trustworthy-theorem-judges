"""TLDR: Reconstruct saved heads, verify training-only preprocessing, and diagnose fit failures."""
import argparse, collections, hashlib, json, math
from pathlib import Path
import numpy as np
from scipy.special import softmax
from scipy.stats import pearsonr, spearmanr, kendalltau
from run_cached import dump

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);a=ap.parse_args();root=Path(a.root)
    d=json.loads((root/'private/dataset.json').read_text());saved=json.loads((root/'private/run/head_forecasts.json').read_text())
    r=json.loads((root/'output/head_results.json').read_text());cfg=json.loads((root/'protocol.json').read_text())
    partitions=json.loads((root/'private/run/bootstrap.json').read_text())['partitions']
    x=np.array([np.mean(d['outputs'][name],axis=1)/5 for name in cfg['candidate_order']]).T
    y=np.array([np.mean(row['ratings'])/5 for row in d['rows']]);n=len(y)
    diagnostics=[]
    for model in saved['models']:
        si=cfg['seeds'].index(model['seed']);outer=np.asarray(partitions[si]['outer']);tr=outer!=model['fold'];te=~tr
        mean=np.asarray(model['mean']);sd=np.asarray(model['sd']);w=np.asarray(model['weights'])
        assert np.allclose(mean,x[tr].mean(0)) and np.allclose(sd,np.maximum(x[tr].std(0),1e-8))
        q=softmax(np.column_stack([np.ones(n),(x-mean)/sd])@w,axis=1);q=(1-6e-6)*q+1e-6
        assert np.allclose(q[te],np.asarray(saved['outputs'][model['loss']][si])[te],atol=1e-12,rtol=1e-12)
        mu=q@(np.arange(6)/5)
        diagnostics.append({'loss':model['loss'],'train_pearson':float(pearsonr(mu[tr],y[tr]).statistic),
                            'test_pearson':float(pearsonr(mu[te],y[te]).statistic),
                            'test_expected_rating_sd':float(mu[te].std()),'test_expected_rating_mean':float(mu[te].mean())})
    checks=0
    for loss,arr in saved['outputs'].items():
        for si,qs in enumerate(arr):
            qs=np.asarray(qs);assert qs.shape==(75,6) and np.all(qs>0) and np.allclose(qs.sum(1),1)
            ce=[];bs=[];rs=[];mu=[]
            for row,q in zip(d['rows'],qs):
                ratings=row['ratings'];ce.append(np.mean([-math.log(q[z]) for z in ratings]))
                bs.append(np.mean([sum((q[k]-int(k==z))**2 for k in range(6)) for z in ratings]))
                rs.append(np.mean([sum((sum(q[:k+1])-int(z<=k))**2 for k in range(5))/5 for z in ratings]))
                mu.append(round(sum(k*q[k]/5 for k in range(6)),12))
            yy=np.round(y,12)
            v={'ce':np.mean(ce),'brier':np.mean(bs),'rps':np.mean(rs),
               'pearson':pearsonr(mu,yy).statistic,'spearman':spearmanr(mu,yy).statistic,'kendall':kendalltau(mu,yy).statistic}
            for k,val in v.items():assert abs(val-r['per_seed'][loss][si][k])<1e-10,(loss,si,k)
            checks+=n
    diag={}
    for loss in saved['outputs']:
        vals=[v for v in diagnostics if v['loss']==loss];fits=[f for f in r['fits'] if f['loss']==loss]
        diag[loss]={k:float(np.mean([v[k] for v in vals])) for k in vals[0] if k!='loss'}
        diag[loss].update(nonconverged=sum(not f['success'] for f in fits),fit_count=len(fits),
                          nonconverged_outer=sum(not f['success'] for f in fits if f['inner_fold'] is None))
    dump(root/'output/head_verification.json',{'status':'PASS','reconstructed_forecasts':checks,'training_only_preprocessing_checks':100,
         'results_sha256':hashlib.sha256((root/'output/head_results.json').read_bytes()).hexdigest(),
         'posthoc_fit_diagnostics':diag})
    print(json.dumps(diag,indent=2))

if __name__=='__main__':main()
