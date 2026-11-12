#!/usr/bin/env python3
"""Bounded two-lane admission; adopt the active V2 cell without restarting it."""
import argparse, datetime, fcntl, hashlib, json, os, subprocess, sys, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
REPO=Path('/Users/brandomiranda/trustworthy-theorem-judges')
RUNNER=REPO/'experiments/09_human_rating_collection/support/scripts/native_packet_generation/claude_code_runner.py'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(p,d):
 q=p.with_suffix('.tmp');q.write_text(json.dumps(d,indent=2)+'\n');q.replace(p)
def live(pid):
 r=subprocess.run(['ps','-p',str(pid),'-o','stat='],capture_output=True,text=True)
 return r.returncode==0 and r.stdout.strip() and not r.stdout.strip().startswith('Z')
def environment():
 code="import json;v={x.split(':')[0]:int(x.split(':')[1].split()[0])*1024 for x in open('/proc/meminfo') if ':' in x};print(json.dumps({'total':v['MemTotal'],'available':v['MemAvailable'],'pressure':open('/proc/pressure/memory').read()}))"
 try:p=subprocess.run(['docker','exec','ttj-native-egress','python','-c',code],capture_output=True,text=True,timeout=15)
 except subprocess.TimeoutExpired:return {'available':0,'probe_error':'Docker VM memory probe timed out'}
 if p.returncode:return {'available':0,'probe_error':p.stderr[-200:]}
 return json.loads(p.stdout)
def pressure_high(e):
 full=0.0
 for line in e.get('pressure','').splitlines():
  if line.startswith('full '):full=float(dict(x.split('=') for x in line.split()[1:])['avg10'])
 return e['available']<1610612736 or full>=1.0
def quota(output):
 latest=[]
 for stream in output.glob('*/stream.jsonl'):
  last=None
  for line in stream.read_text().splitlines():
   try:e=json.loads(line)
   except json.JSONDecodeError:continue
   if e.get('type')=='rate_limit_event':last=e.get('rate_limit_info')
  if last:latest.append(last)
 return {'rejected':any(x.get('status')=='rejected' for x in latest),'maximum_weekly_utilization':max([x.get('unifiedWindows',{}).get('seven_day',{}).get('utilization',0) for x in latest]+[0]),'overage_in_use':any(x.get('isUsingOverage') for x in latest)}
def infra(r):
 errors=json.dumps(r.get('native_result') or {}).lower()
 return r.get('status')!='TERMINAL' or r.get('stop_reason')=='process_exit_without_result' or any(x in errors for x in ['authentication_error','invalid_api_key','oauth token','rate_limit_error','billing_error','credit balance','usage limit']) or (r.get('actual_models') and not r.get('model_identity_verified'))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--amendment',required=True);ap.add_argument('--amendment-sha256',required=True);args=ap.parse_args()
 amend=Path(args.amendment);assert sha(amend)==args.amendment_sha256;a=json.loads(amend.read_text());assert sha(Path(__file__))==a['scheduler_sha256']
 condition=ROOT/'CC_CONDITION_VALID_V2.json';c=json.loads(condition.read_text());assert sha(condition)==a['condition_sha256'];assert sha(RUNNER)==c['runner_sha256']
 manifest=ROOT/'inputs_and_existing/INPUT_MANIFEST.json';assert sha(manifest)==c['input_manifest_sha256']
 output=ROOT/'claude_code_valid_v2';ledger_path=ROOT/'claude_code_readiness/VALID_V2_BATCH_STATUS.json'
 lock=(ROOT/'claude_code_readiness/VALID_V2.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 ledger=json.loads(ledger_path.read_text());ledger.update(pid=os.getpid(),status='RUNNING',scheduler_amendment_sha256=args.amendment_sha256,scheduler_started_at=now(),max_concurrency=2)
 active={};children={};stopped=False
 for task,pid in a['adopted_active_pids'].items():
  assert ledger['tasks'][task]['status']=='RUNNING';active[task]=pid
 save(ledger_path,ledger)
 while True:
  for task,pid in list(active.items()):
   if live(pid):continue
   if task in children:children[task].wait()
   path=output/task/'receipt.json';r=json.loads(path.read_text()) if path.exists() else {'status':'NO_RECEIPT','pid':pid}
   ledger['tasks'][task]=r;del active[task];print(now(),'TERMINAL',task,r.get('status'),r.get('stop_reason'),flush=True)
   if infra(r):stopped=True;ledger.update(admission_stop_reason='INFRASTRUCTURE_OR_IDENTITY',blocked_task=task)
  if not active and all(v['status']=='TERMINAL' for v in ledger['tasks'].values()):
   ledger.update(status='FULL_SET_TERMINAL',finished_at=now());save(ledger_path,ledger);print(now(),'FULL_SET_TERMINAL',flush=True);return
  if stopped and not active:
   ledger.update(status='HELD_AFTER_ACTIVE_DRAIN',updated_at=now());save(ledger_path,ledger);return
  if not stopped and len(active)<2:
   pending=[t for t in c['task_order'] if ledger['tasks'][t]['status']=='PENDING']
   if pending:
    e=environment();q=quota(output);hold=(ROOT/'claude_code_readiness/HOLD_ADMISSIONS').exists()
    ledger['admission_monitor']={'at':now(),'vm':e,'native_quota':q,'external_hold':hold}
    if q['rejected'] or q['overage_in_use'] or q['maximum_weekly_utilization']>=0.85:
     stopped=True;ledger['admission_stop_reason']='QUOTA_OR_FINISHING_RESERVE'
    elif hold or pressure_high(e):ledger['admission_wait_reason']='EXTERNAL_HOLD' if hold else 'VM_MEMORY_PRESSURE'
    else:
     ledger.pop('admission_wait_reason',None)
     for task in pending[:2-len(active)]:
      assert task in a['untouched_task_scope'];assert not (output/task).exists();assert sha(condition)==a['condition_sha256'];assert sha(RUNNER)==c['runner_sha256'];assert sha(manifest)==c['input_manifest_sha256']
      cmd=[sys.executable,str(RUNNER),'run','--manifest',str(manifest),'--condition',str(condition),'--condition-sha256',a['condition_sha256'],'--task-id',task,'--token-file','/Users/brandomiranda/keys/claude_personal_oauth_token.txt','--output-dir',str(output)]
      ledger['tasks'][task]={'status':'RUNNING','started_at':now(),'scheduler_amendment_sha256':args.amendment_sha256};save(ledger_path,ledger)
      print(now(),'ADMIT',task,flush=True);child=subprocess.Popen(cmd,cwd=REPO);children[task]=child;active[task]=child.pid;ledger['tasks'][task]['runner_pid']=child.pid
  ledger['active_pids']=active;ledger['updated_at']=now();save(ledger_path,ledger);time.sleep(10)
if __name__=='__main__':main()
