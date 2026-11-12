#!/usr/bin/env python3
"""TLDR: Report every declared artifact, conditional proper losses and missing-cell bounds without selecting a winner."""
import collections
import json
import math
import random
import statistics
from pathlib import Path
from checker import ROOT, PRIVATE, sha

CONFIG=json.loads((ROOT/'config.json').read_text())

def read(name, default):
    p=PRIVATE/name
    return json.loads(p.read_text()) if p.exists() else default

def mean(xs): return statistics.mean(xs) if xs else None

def interval(values):
    values=sorted(v for v in values if v is not None)
    if not values:return None
    def quantile(p):
        i=(len(values)-1)*p; lo=int(i); hi=math.ceil(i)
        return values[lo]+(values[hi]-values[lo])*(i-lo)
    return [quantile(.025),quantile(.975)]

def bootstrap(rows, metric):
    groups={t:[r for r in rows if r['task']==t] for t in CONFIG['task_ids']}
    rng=random.Random(CONFIG['bootstrap_seed']); values=[]
    for _ in range(CONFIG['bootstrap_draws']):
        sample=[r for t in rng.choices(CONFIG['task_ids'],k=4) for r in groups[t]]
        values.append(metric(sample))
    return {'interval95':interval(values),'valid_resamples':sum(v is not None for v in values),
            'draws':CONFIG['bootstrap_draws'],'unit':'four source-task families, paired configurations',
            'interpretation':'conditional descriptive interval; four purposively selected families cannot establish population precision','p_val':'n/a'}

def score(rows, key):
    pairs=[(r[key],r['target']) for r in rows if r[key] is not None and r['target'] is not None]
    losses=[(q-y)**2 for q,y in pairs]
    out={'observed_pairs':len(pairs),'declared_artifacts':8,'brier':mean(losses),
         'full_denominator_brier_bounds':[sum(losses)/8,(sum(losses)+8-len(losses))/8],
         'mean_probability':mean([q for q,_ in pairs]),'mean_target':mean([y for _,y in pairs]),
         'mean_signed_bias':mean([q-y for q,y in pairs]),'mae_descriptive':mean([abs(q-y) for q,y in pairs])}
    out['brier_bootstrap']=bootstrap(rows,lambda rs:mean([(r[key]-r['target'])**2 for r in rs if r[key] is not None and r['target'] is not None]))
    if len(set(y for _,y in pairs))<2 or len(set(q for q,_ in pairs))<2:
        out['correlations']={'spearman':None,'kendall':None,'pearson':None,'auroc':None,'reason':'fewer than two observed outcome or forecast values'}
    else:
        from scipy import stats
        qs,ys=zip(*pairs)
        positives=[q for q,y in pairs if y==1]; negatives=[q for q,y in pairs if y==0]
        out['correlations']={'spearman':float(stats.spearmanr(qs,ys).statistic),'kendall':float(stats.kendalltau(qs,ys).statistic),'pearson':float(stats.pearsonr(qs,ys).statistic),
                             'auroc':sum((p>n)+.5*(p==n) for p in positives for n in negatives)/(len(positives)*len(negatives)),
                             'interpretation':'descriptive, no inferential correlation claim'}
    return out

def paired_difference(rows, left, right):
    def metric(rs):return mean([(r[left]-r['target'])**2-(r[right]-r['target'])**2 for r in rs if r[left] is not None and r[right] is not None and r['target'] is not None])
    return {'difference':metric(rows),'observed_pairs':sum(r[left] is not None and r[right] is not None and r['target'] is not None for r in rows),'bootstrap':bootstrap(rows,metric)}

def main():
    assert mean([(q-y)**2 for q,y in [(0,0),(1,1)]])==0
    assert mean([(.5-y)**2 for y in [0,1]])==.25
    assert mean([(1-y-y)**2 for y in [0,1]])==1
    artifacts={r['id']:r for r in read('artifacts.json',[])}
    targets={r['artifact']:r for r in read('targets.json',[])}
    forecasts=read('forecasts.json',[])
    primary={(r['artifact'],r['judge']):r for r in forecasts if r['repetition']==0}
    rows=[]
    for t in CONFIG['task_ids']:
        for g in CONFIG['generator']:
            ident=t+'_'+g; a=artifacts.get(ident,{}); target=targets.get(ident,{})
            row={'artifact':ident,'task':t,'generator':g,'generation_status':a.get('generation_status','not_admitted'),
                 'statement_sha256':a.get('statement_sha256'),'context_sha256':a.get('context_sha256'),
                 'target':target.get('target'),'target_status':target.get('status','not_admitted')}
            for j in CONFIG['judge']:
                f=primary.get((ident,j),{});row[j]=f.get('probability');row[j+'_status']=f.get('status','not_admitted')
            for b in CONFIG['fixed_baselines']:row['constant_'+str(b)]=b
            rows.append(row)
    statistics_by_judge={j:score(rows,j) for j in CONFIG['judge']}
    baselines={str(b):score(rows,'constant_'+str(b)) for b in CONFIG['fixed_baselines']}
    comparisons={j+'_minus_constant_'+str(b):paired_difference(rows,j,'constant_'+str(b)) for j in CONFIG['judge'] for b in CONFIG['fixed_baselines']}
    comparisons['J1_minus_J0']=paired_difference(rows,'J1','J0')
    repeats=[]
    for a in CONFIG['repeat_artifacts']:
        for j in CONFIG['judge']:
            qs=[r['probability'] for r in forecasts if r['artifact']==a and r['judge']==j and r['probability'] is not None]
            repeats.append({'artifact':a,'judge':j,'declared_repeats':3,'available_repeats':len(qs),'mean':mean(qs),'sample_sd':statistics.stdev(qs) if len(qs)>1 else None})
    state=read('run_state.json',{}); calls=list(state.get('calls',{}).values()); done=read('done.json',{})
    costs={'provider_cost_usd':0,'reserved_calls':len(calls),'reserved_output_tokens':sum(r['num_predict'] for r in calls),
           'observed_output_tokens_terminal_records':sum(r.get('eval_count') or 0 for r in calls),
           'calls_without_terminal_token_counts':sum(r.get('eval_count') is None for r in calls),
           'thinking_characters_terminal_records':sum(r.get('thinking_characters') or 0 for r in calls),
           'call_status_counts':dict(collections.Counter(r['status'] for r in calls)),
           'failure_category_counts':dict(collections.Counter(r.get('failure_category','none') for r in calls)),
           'wall_seconds':done.get('elapsed_seconds'),'run_status':done.get('status',state.get('status'))}
    y=[r['target'] for r in rows if r['target'] is not None]
    result={'condition':CONFIG['condition'],'artifacts':rows,'availability':{'declared_artifacts':8,'task_families':4,'generated_statements':sum('specification' in a for a in artifacts.values()),
            'unique_statement_hashes':len({a['statement_sha256'] for a in artifacts.values() if a.get('statement_sha256')}),'unique_context_hashes':len({a['context_sha256'] for a in artifacts.values() if a.get('context_sha256')}),'target_available':len(y),'target_successes':sum(y),'target_failures':len(y)-sum(y),'missing_targets':8-len(y),'observed_target_classes':sorted(set(y))},
            'judges':statistics_by_judge,'baselines':baselines,'paired_comparisons':comparisons,'repeat_variability':repeats,'cost':costs,
            'inputs':{name:sha((PRIVATE/name).read_bytes()) for name in ['artifacts.json','forecasts.json','targets.json','run_state.json','done.json'] if (PRIVATE/name).exists()},
            'verdict':'feasibility only; no validated replacement or judge winner',
            'proper_loss_controls':{'oracle':0,'constant_half':.25,'complement':1}}
    (ROOT/'results/analysis.json').write_text(json.dumps(result,indent=2,allow_nan=False)+'\n')
    def fmt(v):return 'unavailable' if v is None else f'{v:.4f}'
    text=['<!-- TLDR: Report the complete eight-artifact pilot, its conditional losses and unresolved larger validation. -->',
          '# Fresh local prover-target judge results','',
          'Status, 11-06-2026: '+str(costs['run_status'])+'. No validated replacement or judge winner is established.','',
          f"The frozen local condition produced {len(y)}/8 available target outcomes ({sum(y)} successes, {len(y)-sum(y)} unsuccessful bounded searches). All eight declared artifacts and four selected task families remain below. The larger frontier target and family-disjoint validation are unfinished.",'',
          '| Artifact | Generation | Target | Target status | J0 probability | J1 probability |','|---|---|---:|---|---:|---:|']
    for r in rows:text.append(f"| {r['artifact']} | {r['generation_status']} | {r['target'] if r['target'] is not None else 'missing'} | {r['target_status']} | {fmt(r['J0'])} | {fmt(r['J1'])} |")
    text+=['','J0/J1 share the same pinned Qwen3.5 9B backbone; thinking is disabled for both; direct/checklist prompts have 256/1,024 output tokens. These are configuration comparisons, not model-family transfer. Only paired available cells enter conditional losses; missing cells are never encoded as zero.','',
           '| Judge | Available pairs / 8 | Conditional Brier | 95% task-family bootstrap interval | Full-denominator Brier bounds | Mean probability | Mean target | Signed bias | Descriptive MAE |',
           '|---|---:|---:|---|---|---:|---:|---:|---:|']
    for j,s in statistics_by_judge.items():
        ci=s['brier_bootstrap']['interval95'];bounds=s['full_denominator_brier_bounds']
        text.append(f"| {j} | {s['observed_pairs']} | {fmt(s['brier'])} | {str([round(v,4) for v in ci]) if ci else 'unavailable'} | {[round(v,4) for v in bounds]} | {fmt(s['mean_probability'])} | {fmt(s['mean_target'])} | {fmt(s['mean_signed_bias'])} | {fmt(s['mae_descriptive'])} |")
    text+=['','Intervals use 10,000 paired resamples of four purposively selected task families (p-val=n/a). They are descriptive and cannot establish population precision. Brier is primary; mean absolute error (MAE) is descriptive. Full-denominator bounds put every missing loss anywhere in [0,1].','',
           'Prespecified constant baselines and paired differences,  correlation availability, exact accounting and input hashes are in [analysis.json](results/analysis.json). If outcome classes or forecasts are constant, correlations and area under the receiver operating characteristic curve are unavailable.','',
           f"Accounting: {costs['reserved_calls']}/48 reserved calls; {costs['reserved_output_tokens']:,}/60,416 requested output tokens; {costs['observed_output_tokens_terminal_records']:,} observed output tokens in terminal receipts; {costs['calls_without_terminal_token_counts']} calls lack terminal token counts. Provider charges: $0. Wall time: {fmt(costs['wall_seconds'])} seconds. Raw local streams and receipts are retained privately.",'',
           'The target requires both consistency and coverage proofs under the frozen bounded procedure. An unsuccessful search is semantically unresolved. Source tasks were previously exposed; newly generated outputs do not make this a fresh-family test. The four cases were selected from a source population with 14 emitted and 86 unresolved contexts out of 100. No full-benchmark score, frontier comparison, human-rating replacement or end-to-end cost-saving claim follows.','',
           '**TLDR-end:** [ttj: fresh local prover-target judges] The complete local pilot ledger and proper-loss accounting are recorded. The larger validation remains pending.']
    (ROOT/'results.md').write_text('\n'.join(text)+'\n')
    print(json.dumps({'availability':result['availability'],'cost':costs,'brier':{j:s['brier'] for j,s in statistics_by_judge.items()}}))

if __name__=='__main__':main()
