"""TLDR: Run the distance extension once, with a ten-minute limit and a terminal receipt."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[1]
data = Path(sys.argv[1]).resolve()
output = root / 'results'
output.mkdir(exist_ok=True)
assert not (output / 'terminal.json').exists()
cfg = json.loads((root / 'protocol.json').read_text())
command = [sys.executable, str(root / 'scripts/run_distances.py'), '--data', str(data),
           '--out', str(output), '--private-out', str(root.parent.parent / 'private')]
stamp = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
receipt = {'started_at': stamp(), 'command': command, 'source_commit': sys.argv[2],
           'dataset_sha256': hashlib.sha256(data.read_bytes()).hexdigest(),
           'protocol_sha256': hashlib.sha256((root / 'protocol.json').read_bytes()).hexdigest(),
           'script_sha256': hashlib.sha256((root / 'scripts/run_distances.py').read_bytes()).hexdigest(),
           'max_wall_seconds': cfg['max_wall_seconds'], 'max_cpu_threads': 1,
           'host': os.uname().nodename, 'new_inference_calls': 0, 'provider_cost_usd': 0}
(output / 'launch.json').write_text(json.dumps(receipt, indent=2) + '\n')
start = time.monotonic()
with (output / 'run.log').open('x') as log:
    try:
        result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT,
                                env={**os.environ, 'OPENBLAS_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1'},
                                timeout=cfg['max_wall_seconds'])
        receipt.update(exit_code=result.returncode,
                       status='COMPLETE' if result.returncode == 0 else 'FAILED')
    except subprocess.TimeoutExpired:
        receipt.update(exit_code=None, status='TIMED_OUT')
receipt.update(finished_at=stamp(), elapsed_seconds=time.monotonic()-start)
if (output / 'results.json').exists():
    receipt['results_sha256'] = hashlib.sha256((output / 'results.json').read_bytes()).hexdigest()
(output / 'terminal.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt), flush=True)
