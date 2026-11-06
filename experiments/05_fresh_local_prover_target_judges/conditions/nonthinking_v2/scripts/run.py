#!/usr/bin/env python3
"""TLDR: Execute a hash-frozen, zero-provider-cost local pilot with durable no-retry call receipts."""
import argparse
import datetime
import fcntl
import hashlib
import json
import os
import signal
import subprocess
import time
import urllib.request
import urllib.error
from pathlib import Path
from checker import Checker, ContextFailure, PRIVATE, ROOT, context, sha

CONFIG=json.loads((ROOT/'config.json').read_text())

class BudgetTimeout(TimeoutError): pass
class IntegrityFailure(RuntimeError): pass

def dump(path, value):
    path.parent.mkdir(parents=True,exist_ok=True)
    temporary=path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n'); temporary.replace(path)

def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()

def read_api(path, payload=None):
    raw=None if payload is None else json.dumps(payload).encode()
    request=urllib.request.Request(CONFIG['endpoint']+'/api/'+path,data=raw,headers={'Content-Type':'application/json'})
    return json.loads(urllib.request.urlopen(request,timeout=10).read())

def check_runtime():
    assert read_api('version')['version']==CONFIG['ollama_version']
    models=read_api('tags')['models']
    row=next(m for m in models if m['name']==CONFIG['model'])
    assert row['digest']==CONFIG['model_digest']
    return {'model':row['name'],'digest':row['digest'],'server_version':CONFIG['ollama_version']}

def verify_freeze():
    freeze=json.loads((ROOT/'sources/freeze.json').read_text())
    assert sha((ROOT.parents[1]/'sources/freeze.json').read_bytes())==freeze['parent_freeze_sha256']
    for file,digest in freeze['files'].items():
        assert sha((ROOT/file).read_bytes())==digest, 'Frozen file changed: '+file
    assert sha((PRIVATE/'cases.json').read_bytes())==freeze['private_case_manifest_sha256']
    for row in json.loads((ROOT/'sources/provenance.json').read_text())['sources']:
        assert sha((PRIVATE/row['destination']).read_bytes())==row['sha256']
    for file,digest in freeze['runtime_dependencies'].items():
        assert sha(Path(file).read_bytes())==digest, 'Runtime dependency changed: '+file
    assert json.loads((ROOT/'results/target_checks.json').read_text())['all_pass']
    return freeze

def journal():
    p=PRIVATE/'run_state.json'
    if p.exists(): return json.loads(p.read_text())
    state={'started_utc':now(),'started_epoch':time.time(),'calls':{},'phase':'preflight','status':'running'}
    dump(p,state); return state

def progress(state, phase):
    state.update(updated_utc=now(),phase=phase,pid=os.getpid())
    dump(PRIVATE/'run_state.json',state)
    public={'phase':phase,'status':state['status'],'updated_utc':state['updated_utc'],
            'reserved_calls':len(state['calls']), 'reserved_generated_tokens':sum(r['num_predict'] for r in state['calls'].values()),
            'finished_calls':sum(r.get('status')=='completed' for r in state['calls'].values()),
            'failed_or_interrupted_calls':sum(r.get('status') not in {'completed','reserved'} for r in state['calls'].values()),
            'provider_cost_usd':0}
    dump(ROOT/'results/live.json',public)

def parse_json(text, field):
    value=json.loads(text)
    assert isinstance(value,dict)
    if field=='probability':
        q=value[field]; assert type(q) in {int,float} and 0<=q<=1
        assert isinstance(value.get('reason'),str)
    else: assert isinstance(value[field],str)
    return value

def call(identity, role, settings, messages, field, seed):
    freeze=verify_freeze(); state=journal()
    assert identity in freeze['planned_calls']
    assert settings['num_predict']==freeze['planned_calls'][identity]['num_predict']
    folder=PRIVATE/'calls'/identity
    if identity in state['calls']:
        result=folder/'receipt.json'
        if result.exists(): return json.loads(result.read_text())
        # A consumed request cannot be replayed after process death.
        record=dict(state['calls'][identity],status='interrupted',failure_category='process_interruption',error='Prior reservation has no terminal receipt')
        dump(result,record); state['calls'][identity]=record; progress(state,role); return record
    parent=json.loads((PRIVATE.parent/'run_state.json').read_text())
    assert (PRIVATE.parent/'done.json').exists(), 'Prior condition still owns execution'
    assert len(parent['calls'])+len(state['calls'])<56
    assert sum(r['num_predict'] for r in list(parent['calls'].values())+list(state['calls'].values()))+settings['num_predict']<=81920
    assert time.time()-parent['started_epoch']<14400
    assert len(state['calls'])<CONFIG['maximum_calls']
    assert sum(r['num_predict'] for r in state['calls'].values())+settings['num_predict']<=CONFIG['maximum_generated_tokens_reserved']
    assert time.time()-state['started_epoch']<CONFIG['execution_wall_seconds']
    runtime=check_runtime()
    schema={'type':'object','properties':{field:{'type':'number' if field=='probability' else 'string'}},'required':[field],'additionalProperties':False}
    if field=='probability':
        schema['properties'][field].update(minimum=0,maximum=1)
        schema['properties']['reason']={'type':'string'}; schema['required'].append('reason')
    request={'model':CONFIG['model'],'messages':messages,'think':settings['think'],'stream':True,
             'format':schema,'keep_alive':'5m','options':{k:CONFIG[k] for k in ['temperature','top_p','top_k','presence_penalty','num_ctx']}}
    request['options'].update(num_predict=settings['num_predict'],seed=seed)
    raw=json.dumps(request,ensure_ascii=False).encode(); folder.mkdir(parents=True,exist_ok=True)
    (folder/'request.json').write_bytes(raw)
    record={'identity':identity,'role':role,'started_utc':now(),'request_sha256':sha(raw),
            'num_predict':settings['num_predict'],'settings':settings,'seed':seed,'status':'reserved','runtime':runtime}
    state['calls'][identity]=record; progress(state,role)
    started=time.monotonic(); content=[]; thinking=[]; final=None
    def expired(*_): raise BudgetTimeout('Hard total model-call wall limit')
    old_handler=signal.signal(signal.SIGALRM,expired)
    signal.setitimer(signal.ITIMER_REAL,CONFIG['call_timeout_seconds'])
    try:
        req=urllib.request.Request(CONFIG['endpoint']+'/api/chat',data=raw,headers={'Content-Type':'application/json'})
        with urllib.request.urlopen(req,timeout=CONFIG['call_timeout_seconds']) as response, (folder/'stream.jsonl').open('wb') as stream:
            for line in response:
                stream.write(line); stream.flush()
                if time.monotonic()-started>CONFIG['call_timeout_seconds']: raise BudgetTimeout('Total model-call wall limit')
                chunk=json.loads(line)
                if 'error' in chunk: raise RuntimeError(chunk['error'])
                if chunk.get('model')!=CONFIG['model']: raise IntegrityFailure('Served model differs from frozen identity')
                content.append(chunk.get('message',{}).get('content',''))
                thinking.append(chunk.get('message',{}).get('thinking',''))
                if chunk.get('done'): final=chunk
        assert final is not None,'Missing terminal model record'
        record.update(done_reason=final.get('done_reason'),eval_count=final.get('eval_count'),
                      prompt_eval_count=final.get('prompt_eval_count'),thinking_characters=sum(map(len,thinking)))
        if record['eval_count']>settings['num_predict']: raise IntegrityFailure('Provider exceeded token cap')
        if record['prompt_eval_count']+settings['num_predict']>CONFIG['num_ctx']: raise IntegrityFailure('Potential context truncation')
        if final.get('done_reason')!='stop': raise ValueError('Generation ended at token limit or abnormal reason')
        record['parsed']=parse_json(''.join(content),field)
        record['status']='completed'
    except Exception as error:
        category=('budget_timeout' if isinstance(error,TimeoutError) or isinstance(getattr(error,'reason',None),TimeoutError) else
                  'integrity_failure' if isinstance(error,IntegrityFailure) else
                  'output_token_budget' if final and final.get('done_reason')=='length' else
                  'transport_failure' if isinstance(error,(urllib.error.URLError,OSError)) else
                  'service_failure' if isinstance(error,RuntimeError) else 'invalid_response')
        record.update(status='failed',failure_category=category,error=type(error).__name__+': '+str(error))
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        signal.signal(signal.SIGALRM,old_handler)
    record.update(seconds=time.monotonic()-started,finished_utc=now(),response_sha256=sha(''.join(content).encode()))
    dump(folder/'receipt.json',record); state=journal(); state['calls'][identity]=record; progress(state,role)
    print(json.dumps({'call':identity,'status':record['status'],'seconds':round(record['seconds'],2),'tokens':record.get('eval_count')}),flush=True)
    if record.get('failure_category')=='integrity_failure': raise IntegrityFailure(record['error'])
    return record

def messages(prompt, data):
    return [{'role':'system','content':prompt},{'role':'user','content':data}]

def preflight():
    results=[]
    for j,settings in CONFIG['judge'].items():
        for index,value in enumerate([0.25,0.75]):
            r=call(f'preflight_{j}_reproduce{index}','preflight',settings,messages('Return JSON with probability exactly equal to the supplied number and a short reason.',str(value)),'probability',CONFIG['base_seed']+index)
            passed=r['status']=='completed' and r['parsed']['probability']==value
            results.append({'identity':r['identity'],'passed':passed,'kind':'probability_reproduction'})
        for index,positive in enumerate([True,False]):
            data=('The fixed tactic proves both goals by identity. CandidateSpec f = (∀ n : Nat, f n = n), GoldSpec f is identical; witness f = id.' if positive else
                  'CandidateSpec f is False, GoldSpec f = (∀ n : Nat, f n = n). Implication is trivial, but the consistency goal ∃f, False is impossible in the trusted kernel.')
            r=call(f'preflight_{j}_semantic{index}','preflight',settings,messages((ROOT/'prompts'/settings['prompt']).read_text(),data),'probability',CONFIG['base_seed']+10+index)
            passed=r['status']=='completed' and (r['parsed']['probability']>=0.8 if positive else r['parsed']['probability']<=0.2)
            results.append({'identity':r['identity'],'passed':passed,'kind':'acceptance_semantics'})
    dump(ROOT/'results/model_preflight.json',{'checks':results,'all_pass':all(r['passed'] for r in results)})
    assert all(r['passed'] for r in results),'Model preflight failed; stop new admissions without retry'

def generate():
    cases=json.loads((PRIVATE/'cases.json').read_text()); artifacts=[]
    for i,case in enumerate(cases):
        source=(PRIVATE/'cases'/case['id']/'Input.py').read_text()
        for g,settings in CONFIG['generator'].items():
            identity=case['id']+'_'+g
            data='PYTHON\n'+source+'\nLEAN INTERFACE\n'+case['signature']
            r=call('generate_'+identity,'generation',settings,messages((ROOT/'prompts'/settings['prompt']).read_text(),data),'specification',CONFIG['base_seed']+100+i*2+int(g[-1]))
            item={'id':identity,'task_id':case['id'],'generator':g,'generation_status':r['status']}
            if r['status']=='completed':
                item['specification']=r['parsed']['specification']
                item['statement_sha256']=sha(item['specification'].encode())
                try: item['context_source']=context(case,item['specification']); item['context_sha256']=sha(item['context_source'].encode())
                except Exception as error: item['invalid_reason']=str(error)
            artifacts.append(item)
            dump(PRIVATE/'artifacts.json',artifacts)
    assert len(artifacts)==8
    dump(ROOT/'results/artifact_hashes.json',[{k:v for k,v in a.items() if k not in {'specification','context_source'}} for a in artifacts])
    dump(ROOT/'results/generation_receipt.json',{'created_utc':now(),'artifacts':8,'private_artifact_sha256':sha((PRIVATE/'artifacts.json').read_bytes())})

def frozen_artifacts():
    receipt=json.loads((ROOT/'results/generation_receipt.json').read_text())
    raw=(PRIVATE/'artifacts.json').read_bytes()
    assert sha(raw)==receipt['private_artifact_sha256']
    rows=json.loads(raw)
    cases={r['id']:r for r in json.loads((PRIVATE/'cases.json').read_text())}
    for a in rows:
        if 'context_source' in a:
            assert a['context_source']==context(cases[a['task_id']],a['specification'])
            assert sha(a['context_source'].encode())==a['context_sha256']
    return rows

def forecasts():
    cases={r['id']:r for r in json.loads((PRIVATE/'cases.json').read_text())}
    outputs=[]
    for a in frozen_artifacts():
        c=cases[a['task_id']]
        for j,settings in CONFIG['judge'].items():
            for repetition in range(3 if a['id'] in CONFIG['repeat_artifacts'] else 1):
                row={'artifact':a['id'],'judge':j,'repetition':repetition,'statement_sha256':a.get('statement_sha256'),
                     'context_sha256':a.get('context_sha256'),'gold_definition_sha256':c['gold_definition_sha256']}
                if 'specification' not in a:
                    row.update(status='missing_candidate',probability=None)
                else:
                    data='PYTHON\n'+(PRIVATE/'cases'/a['task_id']/'Input.py').read_text()+'\nINTERFACE\n'+c['signature']+'\nCANDIDATE PROPOSITION\n'+a['specification']+'\nGOLD PROPOSITIONS\n'+(PRIVATE/'cases'/a['task_id']/'GoldDefinition.txt').read_text()
                    row['input_sha256']=sha(data.encode())
                    r=call('forecast_'+a['id']+'_'+j+'_'+str(repetition),'forecast',settings,messages((ROOT/'prompts'/settings['prompt']).read_text(),data),'probability',CONFIG['base_seed']+200+repetition)
                    row.update(status=r['status'],probability=r.get('parsed',{}).get('probability'),reason=r.get('parsed',{}).get('reason'))
                outputs.append(row);dump(PRIVATE/'forecasts.json',outputs)
    dump(ROOT/'results/forecast_receipt.json',{'created_utc':now(),'forecast_rows':len(outputs),'sha256':sha((PRIVATE/'forecasts.json').read_bytes()),'target_search_started':False})

def targets():
    forecast_receipt=json.loads((ROOT/'results/forecast_receipt.json').read_text())
    assert sha((PRIVATE/'forecasts.json').read_bytes())==forecast_receipt['sha256']
    records=[]
    for a in frozen_artifacts():
        row={'artifact':a['id'],'target':None,'status':'unresolved','goals':{}}
        if 'context_source' not in a:
            row['status']='invalid_or_missing_candidate'
        else:
            try: checker=Checker(PRIVATE/'targets'/a['id'],a['context_source'])
            except ContextFailure as error:
                row.update(status=error.category,error=str(error))
            except (OSError,subprocess.SubprocessError) as error:
                row.update(status='infrastructure_missing',error=str(error))
            else:
                row['context_sha256']=sha(a['context_source'].encode())
                for gi,goal in enumerate(['Natural.Nonvacuous','Natural.Coverage']):
                    tactic='by\n  unfold '+goal+' Natural.AgentSpec'+(' Natural.GoldSpec' if goal.endswith('Coverage') else '')+'\n  first | aesop | omega | grind'
                    checked=checker.check(tactic,goal)
                    detail={'fixed_tactic':checked}
                    if not checked['accepted']:
                        data='CONTEXT\n'+a['context_source']+'\nEXACT GOAL\n'+goal+'\nFIXED TACTIC FAILURE\n'+checked.get('compile',{}).get('output','')[-1500:]
                        r=call('prove_'+a['id']+'_'+str(gi),'proof_search',CONFIG['prover'],messages((ROOT/'prompts/prover.md').read_text(),data),'proof',CONFIG['base_seed']+300+gi)
                        detail['model_call_status']=r['status']
                        if r['status']=='completed':
                            detail['model_proof']=checker.check(r['parsed']['proof'],goal)
                        else:
                            detail['model_failure_category']=r.get('failure_category','process_interruption')
                            detail['model_infrastructure_failure']=detail['model_failure_category'] in {'transport_failure','service_failure','process_interruption','integrity_failure'}
                    detail['accepted']=checked['accepted'] or detail.get('model_proof',{}).get('accepted',False)
                    row['goals'][goal]=detail
                if any(d.get('model_infrastructure_failure') or d['fixed_tactic'].get('status')=='infrastructure_failure' or d.get('model_proof',{}).get('status')=='infrastructure_failure' for d in row['goals'].values()):
                    row['status']='infrastructure_missing'
                else:
                    row['target']=int(all(d['accepted'] for d in row['goals'].values()))
                    row['status']='accepted' if row['target'] else 'bounded_search_unsuccessful'
        records.append(row); dump(PRIVATE/'targets.json',records)
        progress(journal(),'proof_search')
        print(json.dumps({'artifact':a['id'],'target':row['target'],'status':row['status']}),flush=True)
    dump(ROOT/'results/target_receipt.json',{'created_utc':now(),'sha256':sha((PRIVATE/'targets.json').read_bytes()),'rows':len(records)})

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--phase',choices=['all','preflight','generate','forecast','targets'],default='all'); args=parser.parse_args()
    lock=(PRIVATE/'execution.lock').open('w')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    verify_freeze(); check_runtime()
    phases={'preflight':preflight,'generate':generate,'forecast':forecasts,'targets':targets}
    try:
        for name,run in phases.items():
            if args.phase in {'all',name}: run()
        state=journal();state['status']='completed' if args.phase in {'all','targets'} else 'phase_completed';progress(state,args.phase)
    except Exception as error:
        state=journal();state.update(status='stopped',error=type(error).__name__+': '+str(error));progress(state,args.phase);raise

if __name__=='__main__': main()
