#!/usr/bin/env python3
"""Supervise only untouched Pi cells; preserve frozen generation and budgets."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
BATCH = ROOT / 'runs/pi_valid_v3'
POLICY = ROOT / 'PI_ADMISSION_POLICY_V2.json'
POLICY_HASH = '98777eae16d27694c2a1966925b62317a6c78e78623133d7a9cf5b28b19d72c6'
CONDITION = ROOT / 'PI_CONDITION_VALID_V6.json'
INDEX = ROOT / 'pi_task_manifests/VALID_INDEX_V3.json'
OLD_SESSION = 'pi-ttj-native-provider-recovery-01-11-11-2026'
CAP_REASONS = {'Wall-clock budget exhausted', 'Provider request cap reached',
               'Input token cap exceeded', 'Output token cap exceeded',
               'Cell dollar cap cannot admit next request'}

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def utcnow():
    return datetime.datetime.now(datetime.timezone.utc)

def write_state(state):
    state['supervisor_updated_at'] = utcnow().isoformat()
    tmp = BATCH / 'BATCH_STATUS.tmp'
    tmp.write_text(json.dumps(state, indent=2, sort_keys=True) + '\n')
    tmp.replace(BATCH / 'BATCH_STATUS.json')
    (ROOT / 'CKPT_pi_valid_generation.md').write_text(
        '# Native Pi packet generation checkpoint\n\n'
        '**TLDR:** Preserve all 25 original tasks and their one-attempt generation budget. '
        'Continue healthy tasks; use bounded, documented provider recovery.\n\n'
        f'- Updated: {state["supervisor_updated_at"]}\n'
        f'- Status: {state["status"]}\n'
        f'- Current task: {state.get("current_task")}\n'
        f'- Terminal attempts: {len(state["cells"])} / 25\n'
        f'- Pending task IDs: {len(state.get("pending_task_ids", []))}\n'
        f'- Valid conservative cost: ${state["accounted_usd"]:.8f}; invalid pilot $0.7204245 separately.\n'
        f'- Additional recovery admissions used: {state.get("additional_recovery_admissions", 0)} / 2\n'
        f'- Next recovery admission: {state.get("recovery_next_attempt_at", "not scheduled")}\n'
        '- Generation condition: `PI_CONDITION_VALID_V6.json`; admission policy: `PI_ADMISSION_POLICY_V2.json`.\n'
        '- Receipts and trajectories: `runs/pi_valid_v3/<task_id>/`; current state: `runs/pi_valid_v3/BATCH_STATUS.json`.\n'
        '- Never rerun terminal cells, reset counters, infer zero scores for pending tasks, or change models.\n'
        '- Owner: `/root/pi_native_packet`; parent `/root` owns packet preparation and publication.\n')

def classify(cell):
    rp = Path(cell['receipt'])
    lp = rp.with_name('gateway_ledger.json')
    if not rp.exists() or not lp.exists():
        return 'unknown_infrastructure'
    r, ledger = json.loads(rp.read_text()), json.loads(lp.read_text())
    if 'accounted_usd' not in r or 'accounted_usd' not in ledger or cell.get('accounting_missing'):
        return 'unknown_infrastructure'
    denials = ledger.get('denials', [])
    external = [d for d in denials if d['reason'] not in CAP_REASONS]
    if external:
        if all(d.get('upstream_http_status') == 503 or d['reason'] == 'TimeoutError' for d in external):
            return 'service_failure'
        return 'unknown_infrastructure'
    if r['status'] in {'process_completed', 'timeout'}:
        return 'clean'
    if r['status'] == 'provider_error' and denials and all(d['reason'] in CAP_REASONS for d in denials):
        return 'clean'
    return 'unknown_infrastructure'

assert digest(POLICY) == POLICY_HASH
p = json.loads(POLICY.read_text())
assert digest(CONDITION) == p['condition_sha256']
c = json.loads(CONDITION.read_text())
RUNNER = Path(c['runner_snapshot'])
assert digest(RUNNER) == c['runner_sha256']
assert digest(INDEX) == c['task_manifest_index_sha256']
index = json.loads(INDEX.read_text())
assert len(index['cells']) == 25
# Do not become a second writer while the single scheduled recovery task runs.
for _ in range(210):
    if subprocess.run(['tmux', 'has-session', '-t', OLD_SESSION], capture_output=True).returncode:
        break
    time.sleep(10)
else:
    raise RuntimeError('Prior recovery process did not exit within 35 minutes')
state = json.loads((BATCH / 'BATCH_STATUS.json').read_text())
assert len(state['cells']) == 7, 'Expected exactly the first seven terminal attempts'
assert [x['task_id'] for x in state['cells']] == [x['task_id'] for x in index['cells'][:7]]
with (BATCH / 'ADMISSION_POLICY_V2_STARTED.json').open('x') as f:
    json.dump({'started_at': utcnow().isoformat(), 'policy_sha256': POLICY_HASH}, f)
state['admission_policy_sha256'] = POLICY_HASH
state['additional_recovery_admissions'] = 0
state['recovery_admission_history'] = []
state['pending_task_ids'] = [x['task_id'] for x in index['cells'][7:]]
state.pop('recovery_next_attempt_at', None)
state.pop('halt_reason', None)
last_class = classify(state['cells'][-1])
env = os.environ.copy()
env['GEMINI_API_KEY'] = Path.home().joinpath('keys/gemini_allen_key.txt').read_text().strip()
for cell in index['cells'][7:]:
    assert digest(POLICY) == POLICY_HASH
    assert digest(CONDITION) == p['condition_sha256']
    assert digest(RUNNER) == c['runner_sha256']
    assert digest(INDEX) == c['task_manifest_index_sha256']
    assert digest(Path(cell['manifest'])) == cell['manifest_sha256']
    if (ROOT / 'HOLD_NEXT_VALID_PI_CELL').exists():
        state['status'] = 'HELD_BEFORE_NEXT_ADMISSION'
        state['halt_reason'] = (ROOT / 'HOLD_NEXT_VALID_PI_CELL').read_text().strip()
        write_state(state)
        sys.exit(3)
    if last_class == 'unknown_infrastructure':
        state['status'] = 'STOPPED_INFRASTRUCTURE_REVIEW'
        state['halt_reason'] = 'Unknown failure or missing accounting; no automatic further admission'
        write_state(state)
        sys.exit(2)
    is_recovery = last_class == 'service_failure'
    if is_recovery:
        last_receipt = json.loads(Path(state['cells'][-1]['receipt']).read_text())
        due = datetime.datetime.fromisoformat(last_receipt['finished_at']) + datetime.timedelta(seconds=p['cooldown_seconds'])
        cutoff = datetime.datetime.fromisoformat(p['latest_recovery_admission_utc'])
        if state['additional_recovery_admissions'] >= p['maximum_additional_recovery_admissions'] or max(due, utcnow()) > cutoff:
            state['status'] = 'HELD_PROVIDER_UNAVAILABLE'
            state['halt_reason'] = 'Bounded recovery exhausted or admission cutoff reached; remaining tasks are pending provider availability'
            write_state(state)
            sys.exit(4)
        state['status'] = 'COOLDOWN_PROVIDER_RECOVERY'
        state['recovery_next_attempt_at'] = due.isoformat()
        state['current_task'] = None
        write_state(state)
        while utcnow() < due:
            if (ROOT / 'HOLD_NEXT_VALID_PI_CELL').exists():
                state['status'] = 'HELD_BEFORE_NEXT_ADMISSION'
                write_state(state)
                sys.exit(3)
            time.sleep(max(0, min(30, (due - utcnow()).total_seconds())))
        state['additional_recovery_admissions'] += 1
        state['recovery_admission_history'].append({'at': utcnow().isoformat(), 'task_id': cell['task_id']})
    state['status'] = 'RUNNING'
    state['current_task'] = cell['task_id']
    state.pop('recovery_next_attempt_at', None)
    write_state(state)
    out = Path(cell['output_dir'])
    out.mkdir(parents=True, exist_ok=True)
    command = [sys.executable, str(RUNNER), 'run', '--input-dir', cell['input_dir'],
               '--manifest', cell['manifest'], '--manifest-sha256', cell['manifest_sha256'],
               '--image', c['docker_image'], '--output-dir', str(out)]
    print(json.dumps({'event': 'cell_start', 'at': utcnow().isoformat(), 'task_id': cell['task_id'], 'recovery_admission': is_recovery}), flush=True)
    with (out / 'runner_stdout.json').open('x') as stdout, (out / 'runner_stderr.log').open('x') as stderr:
        proc = subprocess.run(command, stdout=stdout, stderr=stderr, env=env)
    rp, lp = out / 'receipt.json', out / 'gateway_ledger.json'
    r = json.loads(rp.read_text()) if rp.exists() else {'status': 'missing_receipt'}
    ledger = json.loads(lp.read_text()) if lp.exists() else {}
    missing = 'accounted_usd' not in r or 'accounted_usd' not in ledger
    cost = .75 if missing else max(float(r['accounted_usd']), float(ledger['accounted_usd']))
    terminal = {'task_id': cell['task_id'], 'status': r['status'], 'artifact_status': r.get('artifact_status', 'missing'),
                'accounted_usd': cost, 'accounting_missing': missing, 'provider_requests': r.get('provider_requests', 0),
                'receipt': str(rp), 'recovery_admission': is_recovery}
    state['cells'].append(terminal)
    state['pending_task_ids'] = [x['task_id'] for x in index['cells'][len(state['cells']):]]
    state['accounted_usd'] = sum(x['accounted_usd'] for x in state['cells'])
    state['global_accounted_usd'] = .7204245 + state['accounted_usd']
    last_class = classify(terminal) if proc.returncode == 0 else 'unknown_infrastructure'
    terminal['completion_class'] = last_class
    if state['accounted_usd'] > c['max_batch_cost_usd'] + 1e-9 or state['global_accounted_usd'] > 20 + 1e-9:
        last_class = 'unknown_infrastructure'
        state['halt_reason'] = 'Unexpected budget excess; stopped'
    write_state(state)
    print(json.dumps({'event': 'cell_end', 'at': utcnow().isoformat(), **terminal}), flush=True)
    if last_class == 'unknown_infrastructure':
        state['status'] = 'STOPPED_INFRASTRUCTURE_REVIEW'
        state.setdefault('halt_reason', 'Unknown failure or missing accounting; stopped')
        write_state(state)
        sys.exit(2)
state['status'] = 'COMPLETED'
state['current_task'] = None
state['finished_at'] = utcnow().isoformat()
write_state(state)
print(json.dumps({'event': 'batch_end', 'cells': len(state['cells']), 'accounted_usd': state['accounted_usd']}), flush=True)
