"""TLDR: Execute the frozen training condition once with a bounded process group and durable receipts."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[1]
data, private, revision = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve(), sys.argv[3]
output = root / 'results'; output.mkdir(exist_ok=True)
assert not (output / 'launch.json').exists(), 'Do not replay an admitted run.'
cfg = json.loads((root / 'protocol.json').read_text())
stamp = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
hash_file = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
files = sorted((root/'scripts').glob('*.py')) + [root/'protocol.json', root/'PROTOCOL.md']
files += [root.parent/'scripts'/name for name in ['metrics.py', 'run_cached.py']]
command = [sys.executable, str(root/'scripts/run_training.py'), '--data', str(data),
           '--out', str(output), '--private-out', str(private)]
receipt = {'started_at': stamp(), 'command': command, 'source_commit': revision,
           'dataset_sha256': hash_file(data), 'protocol_sha256': hash_file(root/'protocol.json'),
           'source_hashes': {str(p.relative_to(root.parent)): hash_file(p) for p in files},
           'max_wall_seconds': cfg['max_wall_seconds'], 'max_cpu_threads': cfg['max_cpu_threads'],
           'host': os.uname().nodename, 'new_inference_calls': 0, 'provider_cost_usd': 0,
           'execution': 'ordinary Python; no model client or API; local LFS files only'}
(output/'launch.json').write_text(json.dumps(receipt, indent=2)+'\n')
start = time.monotonic()
with (output/'run.log').open('x') as log:
    child = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
              env={**os.environ, 'OPENBLAS_NUM_THREADS':'1', 'OMP_NUM_THREADS':'1', 'MKL_NUM_THREADS':'1'})
    receipt['child_pid'] = child.pid
    (output/'launch.json').write_text(json.dumps(receipt, indent=2)+'\n')
    try:
        code = child.wait(timeout=cfg['max_wall_seconds'])
        receipt.update(exit_code=code, status='COMPLETE' if code == 0 else 'FAILED')
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, signal.SIGTERM)
        try: child.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, signal.SIGKILL); child.wait()
        receipt.update(exit_code=child.returncode, status='TIMED_OUT')
receipt.update(finished_at=stamp(), elapsed_seconds=time.monotonic()-start)
if (output/'results.json').exists(): receipt['results_sha256'] = hash_file(output/'results.json')
(output/'terminal.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt), flush=True)
