"""TLDR: Run one bounded cached analysis and persist terminal success or failure evidence."""
import datetime, hashlib, json, os, platform, subprocess, sys, time
from pathlib import Path

root=Path(__file__).resolve().parents[1]
os.chdir(root)
for name in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[name]='1'
start=time.time()
receipt={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'host':platform.node(),
         'pid':os.getpid(),'new_inference_calls':0,'max_wall_seconds':28800,
         'source_revision':(root/'source_revision.txt').read_text().strip(),
         'hashes':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in [root/'protocol.json',root/'private/dataset.json',*sorted((root/'scripts').glob('*.py'))]}}
(root/'output').mkdir(exist_ok=True)
(root/'output/launch.json').write_text(json.dumps(receipt,indent=2)+'\n')
cmd=[sys.executable,'scripts/run_cached.py','--data','private/dataset.json','--config','protocol.json',
     '--out','output','--private-out','private/run']
try:
    with (root/'output/run.log').open('w') as log:
        child=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        receipt['child_pid']=child.pid
        (root/'output/launch.json').write_text(json.dumps(receipt,indent=2)+'\n')
        try:code=child.wait(timeout=28800)
        except subprocess.TimeoutExpired:
            import signal
            os.killpg(child.pid,signal.SIGTERM);child.wait(timeout=30);code=124
    receipt['exit_code']=code
except Exception as e:
    receipt.update(exit_code=1,error=type(e).__name__+': '+str(e))
receipt.update(elapsed_seconds=time.time()-start,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
receipt['status']='COMPLETE' if receipt['exit_code']==0 and (root/'output/results.json').exists() else 'FAILED'
(root/'output/terminal.json').write_text(json.dumps(receipt,indent=2)+'\n')
sys.exit(receipt['exit_code'])
