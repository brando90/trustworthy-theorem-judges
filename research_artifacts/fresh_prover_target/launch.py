import datetime,json,os,signal,subprocess,sys,time
from pathlib import Path
p=Path(__file__).resolve().parent
root=p.parents[1]
started=time.time()
with (p/'execution.log').open('a') as log:
 child=subprocess.Popen([sys.executable,str(root/'experiments/05_fresh_local_prover_target_judges/scripts/run.py'),'--phase','all'],cwd=root,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 (p/'worker.json').write_text(json.dumps({'wrapper_pid':os.getpid(),'child_pid':child.pid,'started_epoch':started})+'\n')
 try: code=child.wait(timeout=14400); status='completed' if code==0 else 'failed'
 except subprocess.TimeoutExpired:
  os.killpg(child.pid,signal.SIGTERM)
  try: code=child.wait(timeout=10)
  except subprocess.TimeoutExpired: os.killpg(child.pid,signal.SIGKILL);code=child.wait()
  status='wall_budget_exhausted'
 (p/'done.json').write_text(json.dumps({'status':status,'exit_code':code,'elapsed_seconds':time.time()-started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})+'\n')
