"""TLDR: Independently reconstruct every selected forecast and per-rater proper loss."""
import argparse, collections, hashlib, json, math
from pathlib import Path
import numpy as np
from scipy.stats import pearsonr, spearmanr, kendalltau

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);a=ap.parse_args();root=Path(a.root)
    data=json.loads((root/'private/dataset.json').read_text())
    result=json.loads((root/'output/results.json').read_text());cfg=json.loads((root/'protocol.json').read_text())
    private=json.loads((root/'private/run/bootstrap.json').read_text())
    assert hashlib.sha256((root/'private/dataset.json').read_bytes()).hexdigest()==cfg['dataset_sha256']
    p=result['primary'];n=len(data['rows']);checked=0
    for oi in p['matrix']:
        values=[]
        for si,seed in enumerate(cfg['seeds']):
            selected={s['fold']:s['candidate'] for s in p['selections'] if s['seed']==seed and s['objective']==oi}
            assert len(selected)==5
            sums=collections.defaultdict(list);xx=[];yy=[]
            for i,row in enumerate(data['rows']):
                name=selected[private['partitions'][si]['outer'][i]];repeat=data['outputs'][name][i]
                q=[(1-6e-6)*repeat.count(k)/3+1e-6 for k in range(6)]
                assert abs(sum(q)-1)<1e-12
                ce=[];brier=[];rps=[]
                for rating in row['ratings']:
                    ce.append(-math.log(q[rating]))
                    brier.append(sum((q[k]-int(k==rating))**2 for k in range(6)))
                    rps.append(sum((sum(q[:k+1])-int(rating<=k))**2 for k in range(5))/5)
                sums['ce'].append(sum(ce)/len(ce));sums['brier'].append(sum(brier)/len(brier));sums['rps'].append(sum(rps)/len(rps))
                xx.append(round(sum(k*q[k]/5 for k in range(6)),12));yy.append(round(sum(row['ratings'])/len(row['ratings'])/5,12))
            v={k:sum(x)/n for k,x in sums.items()};v.update(pearson=float(pearsonr(xx,yy).statistic),spearman=float(spearmanr(xx,yy).statistic),kendall=float(kendalltau(xx,yy).statistic))
            for k,x in v.items():assert abs(x-p['per_seed'][oi][si][k])<1e-10,(oi,si,k)
            values.append(v);checked+=n
        for k in values[0]:assert abs(sum(v[k] for v in values)/5-p['matrix'][oi][k])<1e-10
    assert len(p['selections'])==200
    assert p['bootstrap_draws']==1000 and len(private['ledger'])==1000
    assert sum(x['valid'] for x in private['ledger'])==p['primary_selection_refit_interval']['valid_draws']
    delta=np.asarray(private['selection_refit']);finite=delta[np.isfinite(delta)]
    for k,qt in [('lo',.025),('hi',.975)]:assert abs(float(np.quantile(finite,qt))-p['primary_selection_refit_interval'][k])<1e-12
    receipt={'status':'PASS','independently_reconstructed_artifact_forecasts':checked,'outer_selection_cells':200,
             'completed_bootstrap_draws':1000,'selection_refit_valid_draws':len(finite),
             'proper_score_and_correlation_checks':'direct per-rater formulas and independent SciPy functions',
             'results_sha256':hashlib.sha256((root/'output/results.json').read_bytes()).hexdigest()}
    (root/'output/verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))

if __name__=='__main__':main()
