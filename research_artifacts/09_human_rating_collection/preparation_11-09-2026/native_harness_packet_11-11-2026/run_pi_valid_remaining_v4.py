#!/usr/bin/env python3
"""Execute the parent's frozen 25-cell Pi condition, once per cell, serially."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[3]
RUNNER = REPO / 'experiments/09_human_rating_collection/support/scripts/native_packet_generation/pi_runner.py'
CONDITION = ROOT / 'PI_CONDITION_VALID_V4.json'
INDEX = ROOT / 'pi_task_manifests/VALID_INDEX_V3.json'
CONDITION_HASH = 'e2c20b4fd8632a260da69ba70044ee4a7e8a12e8871d245876d33fe7776d3e3b'
BATCH = ROOT / 'runs/pi_valid_v3'


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def timestamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def save(state):
    BATCH.mkdir(parents=True, exist_ok=True)
    temp = BATCH / 'BATCH_STATUS.tmp'
    temp.write_text(json.dumps(state, indent=2, sort_keys=True) + '\n')
    temp.replace(BATCH / 'BATCH_STATUS.json')
    (ROOT / 'CKPT_pi_valid_generation.md').write_text(
        '# Native Pi packet generation checkpoint\n\n'
        '**TLDR:** Run the frozen 25-task Pi + Gemini 3.8 Flash/high condition. '
        'Preserve every attempt; no silent retries or substitutions.\n\n'
        f'- Updated: {timestamp()}\n'
        f'- Status: {state["status"]}\n'
        f'- Current task: {state.get("current_task", "none")}\n'
        f'- Terminal cells: {len(state["cells"])} / 25\n'
        f'- Valid upper-bound cost: ${state["accounted_usd"]:.6f} / $18.75; invalid pilot $0.7204245 separately\n'
        '- Condition: `PI_CONDITION_VALID_V4.json`\n'
        '- Task index: `pi_task_manifests/VALID_INDEX_V3.json`\n'
        '- Run receipts/trajectories: `runs/pi_valid_v3/<task_id>/`\n'
        '- Watch: `runs/pi_valid_v3/BATCH_STATUS.json`, `runs/pi_valid_v3/driver.log`\n'
        '- Owner: parent `/root`; execution child `/root/pi_native_packet`.\n'
        '- Continue only unstarted frozen cells after diagnosing any infrastructure failure; '
        'never remove an attempt marker or silently rerun a cell.\n'
    )


assert digest(CONDITION) == CONDITION_HASH, 'Condition changed'
c = json.loads(CONDITION.read_text())
assert digest(INDEX) == c['task_manifest_index_sha256'], 'Task index changed'
assert digest(RUNNER) == c['runner_sha256'], 'Runner changed'
index = json.loads(INDEX.read_text())
assert len(index['cells']) == c['task_count'] == 25
assert len({x['task_id'] for x in index['cells']}) == 25
BATCH.mkdir(parents=True, exist_ok=True)
with (BATCH / 'CONTINUATION_V4_STARTED.json').open('x') as f:
    json.dump({'started_at': timestamp(), 'condition_sha256': CONDITION_HASH}, f)
state = json.loads((BATCH / 'BATCH_STATUS.json').read_text())
assert [x['task_id'] for x in state['cells']] == c['prior_attempted_task_ids']
assert [x['task_id'] for x in index['cells'][:len(state['cells'])]] == c['prior_attempted_task_ids']
for completed in state['cells']:
    assert Path(completed['receipt']).exists()
state['condition_lineage'] = [state['condition_sha256'], CONDITION_HASH]
state['condition_sha256'] = CONDITION_HASH
state['status'] = 'RUNNING'
state.pop('halt_reason', None)
completed_count = len(state['cells'])
save(state)
env = os.environ.copy()
env['GEMINI_API_KEY'] = Path.home().joinpath('keys/gemini_allen_key.txt').read_text().strip()
for cell in index['cells'][completed_count:]:
    if state['cells'] and (ROOT / 'HOLD_NEXT_VALID_PI_CELL').exists():
        state['status'] = 'HELD_BEFORE_NEXT_ADMISSION'
        state['halt_reason'] = (ROOT / 'HOLD_NEXT_VALID_PI_CELL').read_text().strip()
        save(state)
        sys.exit(3)
    assert digest(CONDITION) == CONDITION_HASH
    assert digest(INDEX) == c['task_manifest_index_sha256']
    assert digest(RUNNER) == c['runner_sha256']
    assert digest(Path(cell['manifest'])) == cell['manifest_sha256']
    state['current_task'] = cell['task_id']
    save(state)
    output = Path(cell['output_dir'])
    output.mkdir(parents=True, exist_ok=True)
    command = [sys.executable, str(RUNNER), 'run', '--input-dir', cell['input_dir'],
               '--manifest', cell['manifest'], '--manifest-sha256', cell['manifest_sha256'],
               '--image', c['docker_image'], '--output-dir', cell['output_dir']]
    print(json.dumps({'event': 'cell_start', 'at': timestamp(), 'task_id': cell['task_id']}), flush=True)
    with (output / 'runner_stdout.json').open('x') as stdout, (output / 'runner_stderr.log').open('x') as stderr:
        process = subprocess.run(command, stdout=stdout, stderr=stderr, env=env)
    receipt = json.loads((output / 'receipt.json').read_text()) if (output / 'receipt.json').exists() else {'status': 'missing_receipt'}
    ledger = json.loads((output / 'gateway_ledger.json').read_text()) if (output / 'gateway_ledger.json').exists() else {}
    terminal = {'task_id': cell['task_id'], 'status': receipt['status'],
                'artifact_status': receipt.get('artifact_status', 'missing'),
                'accounted_usd': receipt.get('accounted_usd', 0),
                'provider_requests': receipt.get('provider_requests', 0),
                'receipt': str(output / 'receipt.json')}
    state['cells'].append(terminal)
    state['accounted_usd'] = sum(x['accounted_usd'] for x in state['cells'])
    state['global_accounted_usd'] = .7204245 + state['accounted_usd']
    print(json.dumps({'event': 'cell_end', 'at': timestamp(), **terminal}), flush=True)
    known_caps = {'Wall-clock budget exhausted', 'Provider request cap reached',
                  'Input token cap exceeded', 'Output token cap exceeded',
                  'Cell dollar cap cannot admit next request'}
    denials = [x['reason'] for x in ledger.get('denials', [])]
    infra_failure = (process.returncode != 0 or receipt['status'] in {'runner_error', 'missing_receipt', 'no_assistant_response'}
                     or (receipt['status'] == 'provider_error' and any(x not in known_caps for x in denials))
                     or (receipt['status'] == 'provider_error' and not denials))
    if state['accounted_usd'] > c['max_batch_cost_usd'] + 1e-9:
        infra_failure = True
        state['halt_reason'] = 'Batch budget unexpectedly exceeded'
    if infra_failure:
        state['status'] = 'STOPPED_INFRASTRUCTURE_REVIEW'
        state.setdefault('halt_reason', 'Provider/runner failure: investigate before further admission; no cell retry')
        save(state)
        sys.exit(2)
    save(state)
state['status'] = 'COMPLETED'
state['current_task'] = None
state['finished_at'] = timestamp()
save(state)
print(json.dumps({'event': 'batch_end', 'at': timestamp(), 'cells': len(state['cells']), 'accounted_usd': state['accounted_usd']}), flush=True)
