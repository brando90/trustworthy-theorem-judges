#!/usr/bin/env python3
"""TLDR: Verify both immutable freezes, shared budgets, forecast-before-target order and exact receipt-to-score bindings."""
import datetime
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PRIVATE=ROOT.parents[1]/'private/fresh_prover_target'

def sha(data):return hashlib.sha256(data).hexdigest()
def load(path):return json.loads(path.read_text())
def timestamp(t):return datetime.datetime.fromisoformat(t).timestamp()

def main():
    pairs=[(ROOT,PRIVATE),(ROOT/'conditions/nonthinking_v2',PRIVATE/'v2')]
    states=[]; checks=[]
    for exp,private in pairs:
        freeze=load(exp/'sources/freeze.json');config=load(exp/'config.json')
        for name,digest in freeze['files'].items():assert sha((exp/name).read_bytes())==digest,name
        for name,digest in freeze['runtime_dependencies'].items():assert sha(Path(name).read_bytes())==digest,name
        assert sha((private/'cases.json').read_bytes())==freeze['private_case_manifest_sha256']
        provenance=load(exp/'sources/provenance.json')
        for item in provenance['sources']:assert sha((private/item['destination']).read_bytes())==item['sha256']
        for stem,receipt_name,hash_key in [('artifacts','generation','private_artifact_sha256'),('targets','target','sha256')]:
            raw=private/(stem+'.json');receipt=exp/'results'/(receipt_name+'_receipt.json')
            if raw.exists():assert sha(raw.read_bytes())==load(receipt)[hash_key]
            else:assert not receipt.exists()
        if (private/'artifacts.json').exists():
            projected=[{k:v for k,v in a.items() if k not in {'specification','context_source'}} for a in load(private/'artifacts.json')]
            assert projected==load(exp/'results/artifact_hashes.json')
        state=load(private/'run_state.json');states.append(state)
        for identity,record in state['calls'].items():
            assert identity in freeze['planned_calls']
            receipt=load(private/'calls'/identity/'receipt.json')
            assert record==receipt
            request=(private/'calls'/identity/'request.json').read_bytes()
            assert sha(request)==record['request_sha256']
            assert record['num_predict']==freeze['planned_calls'][identity]['num_predict']
            assert record['runtime']['model']==config['model'] and record['runtime']['digest']==config['model_digest']
            if record.get('eval_count') is not None:assert record['eval_count']<=record['num_predict']
            if record['status']=='completed':assert record['done_reason']=='stop'
        checks.append({'condition':config['condition'],'frozen_files':len(freeze['files']),'call_receipts':len(state['calls']),'freeze_matches':True})
    v2=PRIVATE/'v2'; exp2=ROOT/'conditions/nonthinking_v2'
    artifacts=load(v2/'artifacts.json'); forecasts=load(v2/'forecasts.json'); targets=load(v2/'targets.json')
    assert len(artifacts)==len(targets)==8 and len(forecasts)==16
    assert {a['id'] for a in artifacts}=={t+'_'+g for t in load(exp2/'config.json')['task_ids'] for g in ['G0','G1']}
    assert len({(f['artifact'],f['judge'],f['repetition']) for f in forecasts})==16
    assert all(f['repetition']==0 for f in forecasts)
    fseal=load(exp2/'results/forecast_receipt.json')
    assert sha((v2/'forecasts.json').read_bytes())==fseal['sha256']
    seal_time=timestamp(fseal['created_utc'])
    for r in states[1]['calls'].values():
        if r['role']=='forecast': assert timestamp(r['finished_utc'])<=seal_time
        if r['role']=='proof_search': assert timestamp(r['started_utc'])>=seal_time
    for f in forecasts:
        if f['status']=='missing_candidate':assert f['probability'] is None;continue
        identity='forecast_'+f['artifact']+'_'+f['judge']+'_0'
        request=load(v2/'calls'/identity/'request.json')
        assert sha(request['messages'][1]['content'].encode())==f['input_sha256']
        receipt=load(v2/'calls'/identity/'receipt.json')
        assert f['probability']==receipt.get('parsed',{}).get('probability')
        assert f['statement_sha256']==next(a['statement_sha256'] for a in artifacts if a['id']==f['artifact'])
    for t in targets:
        if t['target']==1:
            assert len(t['goals'])==2 and all(g['accepted'] for g in t['goals'].values())
            for g in t['goals'].values():
                proof=g['fixed_tactic'] if g['fixed_tactic']['accepted'] else g['model_proof']
                assert proof['status']=='accepted' and proof['protected_intact'] and proof['olean_unchanged']
                r=proof['records'][0];assert r['typeExact'] and r['replayed'] and not r['collisions']
                assert set(r['axioms'])<={'propext','Classical.choice','Quot.sound'}
        elif t['target']==0:assert t['status']=='bounded_search_unsuccessful'
        else:assert t['status'] in {'invalid_context','invalid_or_missing_candidate','infrastructure_missing'}
    calls=[r for state in states for r in state['calls'].values()]
    assert len(calls)<=56 and sum(r['num_predict'] for r in calls)<=81920
    end=load(v2/'done.json');assert end['shared_elapsed_seconds']<=14420
    result={'all_pass':True,'conditions':checks,'artifact_rows':8,'primary_forecast_rows':16,
            'forecast_seal_precedes_model_target_calls':True,'generation_and_target_hashes_match':True,'artifact_hash_projection_matches':True,'private_source_hashes_match':True,'shared_calls':len(calls),'shared_requested_tokens':sum(r['num_predict'] for r in calls),
            'shared_elapsed_seconds':end['shared_elapsed_seconds'],'provider_cost_usd':0,
            'note':'Exact receipt checks; no new inference, no proof-search retries.'}
    (ROOT/'results/verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__=='__main__':main()
