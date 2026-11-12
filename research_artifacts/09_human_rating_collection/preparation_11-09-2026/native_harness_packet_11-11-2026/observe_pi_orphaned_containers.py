#!/usr/bin/env python3
"""Observe two existing Pi conversations; no generation/restart commands exist here."""
from pathlib import Path
import subprocess,json,datetime,time,hashlib,os
ROOT=Path(__file__).resolve().parent
BATCH=ROOT/'runs/pi_valid_v3'
CELLS={'cs_set__topological_sort':'c82d4f5ffc7e','humaneval_set__humaneval_39_prime_fib':'12505ab066cd'}
def now():return datetime.datetime.now(datetime.timezone.utc)
def write(p,v):p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def docker(*a):return subprocess.run(['docker',*a],capture_output=True,text=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 state={'observer_pid':os.getpid(),'observer_sha256':sha(Path(__file__)),'started_at':now().isoformat(),'no_restarts_or_new_generation':True,'cells':{}}
 for task,suffix in CELLS.items():
  out=BATCH/task;r=json.loads((out/'receipt.json').read_text());backup=out/'receipt_before_host_supervision_recovery.json'
  if not backup.exists():backup.write_bytes((out/'receipt.json').read_bytes())
  deadline=datetime.datetime.fromisoformat(r['started_at'])+datetime.timedelta(seconds=r['wall_seconds'])
  state['cells'][task]={'solver':'ttj-pi-solver-'+suffix,'gateway':'ttj-pi-gateway-'+suffix,'network':'ttj-pi-net-'+suffix,'deadline_utc':deadline.isoformat(),'status':'observing_existing_conversation','original_receipt_sha256':sha(backup)}
 write(ROOT/'PI_LIVE_CONTAINER_RECOVERY_STATUS.json',state)
 remaining=set(CELLS)
 while remaining:
  for task in list(remaining):
   cell=state['cells'][task];out=BATCH/task
   top=docker('top',cell['solver'],'-eo','pid,comm').stdout
   live=any(x.split()[-1:] in [['pi'],['node']] for x in top.splitlines()[1:])
   expired=now()>=datetime.datetime.fromisoformat(cell['deadline_utc'])
   docker('cp',cell['gateway']+':/tmp/gateway_ledger.json',str(out/'gateway_ledger_recovery_live.json'))
   if live and not expired:continue
   if expired:docker('stop','--time','2',cell['solver'])
   docker('cp',cell['solver']+':/tmp/pi-sessions',str(out/'pi-sessions_recovered'))
   r=json.loads((out/'receipt_before_host_supervision_recovery.json').read_text())
   manifest=json.loads((ROOT/'pi_task_manifests'/f'{task}.json').read_text());candidate=out/'candidate.lean'
   copied=docker('cp',cell['solver']+':/home/user/lean_project/'+manifest['output_file'],str(candidate))
   r['artifact_status']='missing'
   if copied.returncode==0 and candidate.is_file() and not candidate.is_symlink():
    r.update({'artifact_status':'present' if candidate.read_bytes().strip() else 'empty','artifact_sha256':sha(candidate),'artifact_bytes':candidate.stat().st_size,'candidate_file':'candidate.lean'})
   docker('cp',cell['gateway']+':/tmp/gateway_ledger.json',str(out/'gateway_ledger.json'))
   ledger=json.loads((out/'gateway_ledger.json').read_text());messages=[]
   for f in (out/'pi-sessions_recovered').rglob('*.jsonl'):
    for line in f.read_text().splitlines():
     try:v=json.loads(line)
     except ValueError:continue
     if v.get('message',{}).get('role')=='assistant':messages.append(v['message'])
   final=messages[-1] if messages else {}
   r.update({'status':'timeout' if expired else 'recovered_native_terminal','provider_requests':len(ledger['requests']),'accounted_usd':ledger['accounted_usd'],'native_stop_reason':final.get('stopReason'),'actual_model':final.get('model'),'actual_provider':final.get('provider'),'actual_thinking':final.get('thinkingLevel'),'finished_at':now().isoformat(),'elapsed_seconds':round((now()-datetime.datetime.fromisoformat(r['started_at'])).total_seconds(),3),'supervision_recovery':{'incident':'Host wrappers ended when their tmux coordinator exited. Existing Docker Pi processes and gateways continued; neither conversation was restarted.','observer_path':str(Path(__file__)),'observer_sha256':sha(Path(__file__)),'original_receipt_path':str(out/'receipt_before_host_supervision_recovery.json'),'original_receipt_sha256':cell['original_receipt_sha256'],'original_deadline_utc':cell['deadline_utc'],'trajectory_caveat':'Original host trajectory is incomplete after wrapper loss; native persisted sessions are preserved separately in pi-sessions_recovered. No candidate was reconstructed.','infrastructure_affected':True}})
   write(out/'receipt.json',r);cell.update({'status':'terminal_supervision_recovered','native_process_deadline_reached':expired,'accounted_usd':r['accounted_usd'],'artifact_status':r['artifact_status'],'receipt_sha256':sha(out/'receipt.json')});remaining.remove(task)
   for name in [cell['solver'],cell['gateway']]:docker('rm','-f',name)
   docker('network','rm',cell['network'])
  state['updated_at']=now().isoformat();write(ROOT/'PI_LIVE_CONTAINER_RECOVERY_STATUS.json',state)
  if remaining:time.sleep(2)
 state['status']='both_original_conversations_terminal';state['finished_at']=now().isoformat();write(ROOT/'PI_LIVE_CONTAINER_RECOVERY_STATUS.json',state)
if __name__=='__main__':main()
