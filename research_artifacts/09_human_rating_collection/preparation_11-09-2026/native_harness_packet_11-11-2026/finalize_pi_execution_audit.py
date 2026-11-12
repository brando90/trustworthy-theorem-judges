#!/usr/bin/env python3
"""Read terminal receipts and emit a final audit; no inference or artifact rewriting."""
from pathlib import Path
from decimal import Decimal
import json,hashlib,datetime,collections
ROOT=Path(__file__).resolve().parent
BATCH=ROOT/'runs/pi_valid_v3'
def read(p):return json.loads(p.read_text())
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def accounting(ledger):
 completed=sum((Decimal(str(q['charged_upper_bound_usd'])) for q in ledger['requests'] if 'charged_upper_bound_usd' in q),Decimal(0))
 unresolved=sum((Decimal(str(q['reserved_usd'])) for q in ledger['requests'] if 'charged_upper_bound_usd' not in q),Decimal(0))
 assert abs(completed+unresolved-Decimal(str(ledger['accounted_usd'])))<Decimal('0.00000001')
 return completed,unresolved
def main():
 state=read(BATCH/'BATCH_STATUS.json');assert state['status']=='COMPLETED' and len(state['cells'])==25 and not state['active_workers'] and not state['pending_task_ids']
 index=read(ROOT/'pi_task_manifests/VALID_INDEX_V3.json')['cells'];assert len(index)==25
 records=[];completed_total=Decimal(0);unresolved_total=Decimal(0)
 for cell in index:
  out=Path(cell['output_dir']);r=read(out/'receipt.json');ledger=read(out/'gateway_ledger.json');manifest=read(Path(cell['manifest']))
  assert r.get('finished_at') and r['status']!='running' and r['attempts']==1
  assert digest(Path(cell['manifest']))==r['manifest_sha256']==cell['manifest_sha256']
  assert r['input_files']==manifest['files'] and r['host_mounts']==[] and r['runtime_uid']==1001
  assert r['pi_version_observed']=='1.5.2' and r['model']=='gemini-3.8-flash' and r['thinking']=='high'
  assert r['image_id']=='sha256:2104a4b8fe86379143a49331d79c9eecae67ab58ef73d4db05183510061bc89e'
  assert r['cell_cap_usd']==.75 and r['request_cap']==40 and r['wall_seconds']==1800
  assert len(ledger['requests'])==r['provider_requests']<=40
  charged,reserved=accounting(ledger);completed_total+=charged;unresolved_total+=reserved
  assert charged+reserved<=Decimal('.75')+Decimal('.00000001')
  prompt=Path(cell['input_dir'])/manifest['prompt_file'];instruction=prompt.read_text();assert digest(prompt)==manifest['files'][manifest['prompt_file']]
  sessions=list((out/'pi-sessions_recovered').rglob('*.jsonl')) or list((out/'pi-sessions').rglob('*.jsonl'));verbatim=False;tool_counts=collections.Counter();write_paths=set();session_records=[]
  for session in sessions:
   session_records.append({'path':str(session),'sha256':digest(session)})
   for line in session.read_text().splitlines():
    event=json.loads(line);msg=event.get('message',{})
    if msg.get('role')=='user':
     text='\n'.join(x.get('text','') for x in msg.get('content',[]) if x.get('type')=='text')
     verbatim=verbatim or instruction in text
    for part in msg.get('content',[]):
     if part.get('type')=='toolCall':
      tool_counts[part.get('name')]+=1
      if part.get('name') in ['write','edit']:write_paths.add(part.get('arguments',{}).get('path',''))
  assert verbatim and manifest['output_file'] in instruction
  runner=next(p for p in (ROOT/'pi_runner_versions').glob('*.py') if digest(p)==r['runner_sha256'])
  assert 'solver + ":" + WORKSPACE + "/" + manifest["output_file"]' in runner.read_text()
  if r['artifact_status']=='present':assert digest(out/'candidate.lean')==r['artifact_sha256']
  reasons=list(dict.fromkeys(x['reason'] for x in ledger['denials']))
  if r['status']=='timeout':reasons.append('Original wall-clock cap')
  if r.get('native_stop_reason')=='length':reasons.append('Native output-length stop / provider MAX_TOKENS')
  if r.get('supervision_recovery'):reasons.append('Host-wrapper-loss incident; original Docker conversation recovered without restart')
  if not reasons:reasons.append('Native process ended without required artifact' if r['artifact_status']=='missing' else 'Native terminal outcome')
  records.append({'task_id':r['task_id'],'status':r['status'],'native_stop_reason':r.get('native_stop_reason'),'artifact_status':r['artifact_status'],'causes':reasons,'denials':ledger['denials'],'generation_requests_including_retries':len(ledger['requests']),'completed_usage_cost_upper_bound_usd':float(charged),'unresolved_request_reservations_usd':float(reserved),'conservative_usd':float(charged+reserved),'receipt_path':str(out/'receipt.json'),'receipt_sha256':digest(out/'receipt.json'),'gateway_ledger_sha256':digest(out/'gateway_ledger.json'),'runner_snapshot_path':str(runner),'runner_sha256':r['runner_sha256'],'original_started_at':r['started_at'],'finished_at':r['finished_at'],'required_output_absolute':'/home/user/lean_project/'+manifest['output_file'],'prompt_verbatim_in_native_session':verbatim,'native_sessions':session_records,'native_tool_counts':dict(tool_counts),'write_edit_paths':sorted(write_paths),'provider_returned_model_versions':sorted(set(q['model_version'] for q in ledger['requests'] if q.get('model_version'))),'supervision_recovery':r.get('supervision_recovery')})
 pilot=read(ROOT/'runs/pi/realcode_set__20_html_escape/gateway_ledger.json');pc,pu=accounting(pilot);combined=completed_total+unresolved_total+pc+pu;assert combined<=20
 report={'completed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'all25_original_tasks_terminal','task_count':25,'attempted_once':25,'pending':0,'captured_required_path_artifacts':sum(r['artifact_status']=='present' for r in records),'native_harness':'Pi','native_version':'1.5.2','model':'gemini-3.8-flash','thinking':'high','payer_scope':'Existing Allen Google key, VeriBench scope','caps_per_cell':{'generation_requests_including_generation_retries':40,'wall_seconds':1800,'input_tokens_per_request':65536,'output_tokens_per_request':16384,'conservative_usd':.75},'counter_definition':'The receipt provider_requests alias counts generation requests including generation retries. countTokens preflights are separate HTTP calls and are not individually counted by that ledger.','generation_requests_total':sum(r['generation_requests_including_retries'] for r in records),'completed_usage_cost_upper_bound_usd':float(completed_total),'unresolved_request_reservations_usd':float(unresolved_total),'valid_cohort_conservative_usd':float(completed_total+unresolved_total),'invalid_environment_pilot':{'generation_requests':len(pilot['requests']),'completed_usage_cost_upper_bound_usd':float(pc),'unresolved_request_reservations_usd':float(pu),'conservative_usd':float(pc+pu),'excluded_from25':True},'combined_conservative_usd':float(combined),'global_ceiling_usd':20,'cost_interpretation':'Cost bounds from returned usage, ignoring cache discounts, plus full reservations for incomplete/failed requests. These are not verified invoice charges.','source_and_egress_audit':{'verbatim_frozen_prompt_verified':25,'capture_path_matches_instruction':25,'runtime_uid':1001,'host_mounts':[],'clean_image':'sha256:2104a4b8fe86379143a49331d79c9eecae67ab58ef73d4db05183510061bc89e','contract':'Frozen runner asserts an internal-only solver network. A separate gateway permits only the pinned Google generation route, with native function tools and HIGH thinking. Actual first concurrent runtime inspections are preserved in PI_V7_FIRST_TWO_RUNTIME_ISOLATION.json.','limitation':'Whole workspace snapshots were not retained; zero captured required-path artifacts does not mean no temporary Lean code was written elsewhere.'},'records':records}
 (ROOT/'PI_FINAL_EXECUTION_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
 lines=['# Native Pi generation: final audit','',f'**TLDR:** All 25 original Pi attempts are terminal; {report["captured_required_path_artifacts"]} required-path artifacts were captured. Every attempt and failure is preserved; no task was retried.','',f'Native Pi 1.5.2 used `gemini-3.8-flash` with high thinking under the frozen per-cell caps: 40 generation requests including generation retries, 1,800 seconds, 65,536 input tokens, 16,384 output tokens, and $0.75. Token-counting preflights are additional HTTP calls, outside the generation-request counter.','',f'Valid-cohort conservative cost: ${completed_total+unresolved_total:.8f}, comprising ${completed_total:.8f} completed-usage upper bounds and ${unresolved_total:.8f} unresolved request reservations. Invalid environment pilot: ${pc+pu:.8f}, separately excluded. Combined: ${combined:.8f} against the $20 ceiling. Cache discounts are ignored; this is not an invoice.','', '[Full evidence and per-task receipts](PI_FINAL_EXECUTION_AUDIT.json). The separate [output-path diagnostic](PI_OUTPUT_CAPTURE_DIAGNOSTIC.md) explains why the conclusion concerns required-path submissions. The two recovered host-wrapper cases retain their original conversations, deadlines, native sessions and explicit incident provenance.','', '| Task | Captured file | Generation requests | Terminal causes |','|---|---:|---:|---|']
 for row in records:lines.append(f'| `{row["task_id"]}` | {row["artifact_status"]} | {row["generation_requests_including_retries"]} | '+ '; '.join(row['causes'])+' |')
 (ROOT/'PI_FINAL_EXECUTION_AUDIT.md').write_text('\n'.join(lines)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['records','source_and_egress_audit']},indent=2))
if __name__=='__main__':main()
