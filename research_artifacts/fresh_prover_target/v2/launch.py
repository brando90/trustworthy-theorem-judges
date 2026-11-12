import datetime,json,os,signal,subprocess,sys,time
from pathlib import Path
p=Path(__file__).resolve().parent
root=p.parents[2]
parent=json.loads((p.parent/'run_state.json').read_text())
deadline=parent['started_epoch']+14400
(p/'worker.json').write_text(json.dumps({'wrapper_pid':os.getpid(),'state':'waiting_for_v1_completion','shared_deadline_epoch':deadline})+'\n')
while not (p.parent/'done.json').exists():
 if time.time()>=deadline:raise RuntimeError('Shared wall ceiling reached')
 time.sleep(1)
started=time.time()
with (p/'execution.log').open('a') as log:
 child=subprocess.Popen([sys.executable,str(root/'experiments/05_fresh_local_prover_target_judges/conditions/nonthinking_v2/scripts/run.py'),'--phase','all'],cwd=root,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 (p/'worker.json').write_text(json.dumps({'wrapper_pid':os.getpid(),'child_pid':child.pid,'started_epoch':started,'shared_deadline_epoch':deadline})+'\n')
 try: code=child.wait(timeout=max(1,deadline-time.time()));status='completed' if code==0 else 'failed'
 except subprocess.TimeoutExpired:
  os.killpg(child.pid,signal.SIGTERM)
  try:code=child.wait(timeout=10)
  except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);code=child.wait()
  status='wall_budget_exhausted'
 (p/'done.json').write_text(json.dumps({'status':status,'exit_code':code,'elapsed_seconds':time.time()-started,'shared_elapsed_seconds':time.time()-parent['started_epoch'],'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})+'\n')
