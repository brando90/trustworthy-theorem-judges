#!/usr/bin/env python3
"""One coordinator, at most four isolated workers, immutable task attempts."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
BATCH = ROOT / 'runs/pi_valid_v3'
CONDITION = ROOT / 'PI_CONDITION_VALID_V8.json'
CONDITION_HASH = '4cfe4649b8570395787113aa6780ada2b0d2d71230ee9ee3436caf775f6f67f9'
INDEX = ROOT / 'pi_task_manifests/VALID_INDEX_V3.json'
MEMORY_MIN_BYTES = 1536 * 1024 * 1024
CAP_REASONS = {'Wall-clock budget exhausted', 'Provider request cap reached', 'Input token cap exceeded',
               'Output token cap exceeded', 'Cell dollar cap cannot admit next request'}

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def utcnow():
    return datetime.datetime.now(datetime.timezone.utc)

def read_json(p):
    return json.loads(p.read_text())

def persist(state):
    state['supervisor_updated_at'] = utcnow().isoformat()
    tmp = BATCH / 'BATCH_STATUS.tmp'
    tmp.write_text(json.dumps(state, indent=2, sort_keys=True) + '\n')
    tmp.replace(BATCH / 'BATCH_STATUS.json')
    (ROOT / 'CKPT_pi_valid_generation.md').write_text(
        '# Native Pi packet generation checkpoint\n\n'
        '**TLDR:** Finish the original 25-task cohort with at most four isolated workers. '
        'Preserve every attempt, all caps, and explicit provider-unavailable outcomes.\n\n'
        f'- Updated: {state["supervisor_updated_at"]}\n'
        f'- Status: {state["status"]}\n'
        f'- Terminal attempts: {len(state["cells"])} / 25\n'
        f'- Active task IDs: {list(state.get("active_workers", {}))}\n'
        f'- Untouched tasks: {len(state.get("pending_task_ids", []))}\n'
        f'- Valid conservative cost: ${state["accounted_usd"]:.8f}; invalid pilot $0.7204245 separately.\n'
        f'- Active full-cap reservations: ${state.get("active_reservations_usd", 0):.2f}\n'
        f'- Additional outage-recovery admissions: {state.get("additional_recovery_admissions", 0)} / 2\n'
        f'- Next recovery admission: {state.get("recovery_next_attempt_at", "not scheduled")}\n'
        '- Condition: `PI_CONDITION_VALID_V8.json`; per-cell runner remains the frozen V6 snapshot.\n'
        '- Receipts and trajectories: `runs/pi_valid_v3/<task_id>/`.\n'
        '- Never rerun terminal tasks or treat pending tasks as zero scores.\n')

def terminal_record(cell):
    out = Path(cell['output_dir'])
    rp, lp = out / 'receipt.json', out / 'gateway_ledger.json'
    try:
        r = read_json(rp) if rp.exists() else {'status': 'missing_receipt'}
    except (ValueError, OSError):
        r = {'status': 'unreadable_receipt'}
    try:
        ledger = read_json(lp) if lp.exists() else {}
    except (ValueError, OSError):
        ledger = {}
    missing = 'accounted_usd' not in r or 'accounted_usd' not in ledger
    cost = .75 if missing else max(float(r['accounted_usd']), float(ledger['accounted_usd']))
    record = {'task_id': cell['task_id'], 'status': r['status'], 'artifact_status': r.get('artifact_status', 'missing'),
              'accounted_usd': cost, 'accounting_missing': missing, 'provider_requests': r.get('provider_requests', 0),
              'receipt': str(rp)}
    external = [d for d in ledger.get('denials', []) if d['reason'] not in CAP_REASONS]
    if missing:
        kind = 'unknown_infrastructure'
    elif external:
        kind = 'service_failure' if all(d.get('upstream_http_status') == 503 or d['reason'] == 'TimeoutError' for d in external) else 'unknown_infrastructure'
    elif r['status'] in {'process_completed', 'timeout'} or (r['status'] == 'provider_error' and ledger.get('denials')):
        kind = 'clean'
    else:
        kind = 'unknown_infrastructure'
    record['completion_class'] = kind
    return record, r, ledger

def pending_ids(index, completed, active):
    return [c['task_id'] for c in index if c['task_id'] not in completed and c['task_id'] not in active]

def reservation_ok(completed_cost, active_count):
    return .7204245 + completed_cost + .75 * (active_count + 1) <= 20 + 1e-9

def resource_snapshot(image):
    code = "from pathlib import Path; import time,json; read=lambda:list(map(int,Path('/proc/stat').read_text().splitlines()[0].split()[1:])); a=read(); time.sleep(5); b=read(); d=[y-x for x,y in zip(a,b)]; print(json.dumps({'memory_available_bytes':int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])*1024,'cpu_busy_fraction':1-(d[3]+d[4])/sum(d[:8]),'sample_seconds':5}))"
    out = subprocess.check_output(['docker', 'run', '--rm', '--network', 'none', '--user', 'user', image,
                                   'python3', '-c', code], text=True)
    return json.loads(out)


def resource_admission_allowed(resources):
    return resources['memory_available_bytes'] >= MEMORY_MIN_BYTES and resources['cpu_busy_fraction'] < .85


class AdoptedProcess:
    """Monitor the exact surviving runner without interrupting or reparenting it."""
    def __init__(self, pid, runner, out):
        self.pid, self.runner, self.out = pid, str(runner), out

    def poll(self):
        result = subprocess.run(['ps', '-p', str(self.pid), '-o', 'command='], capture_output=True, text=True)
        if result.returncode == 0 and self.runner in result.stdout and str(self.out) in result.stdout:
            return None
        try:
            r = read_json(self.out / 'receipt.json')
            return 0 if r.get('status') != 'running' and r.get('finished_at') else 1
        except (ValueError, OSError):
            return 1

def main():
    assert digest(CONDITION) == CONDITION_HASH
    c = read_json(CONDITION)
    assert digest(INDEX) == c['task_manifest_index_sha256']
    runner = Path(c['runner_snapshot'])
    assert digest(runner) == c['runner_sha256']
    index = read_json(INDEX)['cells']
    assert len(index) == len({x['task_id'] for x in index}) == 25
    by_id = {x['task_id']: x for x in index}
    order = {x['task_id']: n for n, x in enumerate(index)}
    lock = (BATCH / 'COORDINATOR.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    # The prior coordinator is stopped by PID only; all live task runners survive unchanged.
    state = read_json(BATCH / 'BATCH_STATUS.json')
    assert state['condition_sha256'] == c['prior_condition_sha256']
    assert state['status'] == 'RUNNING'
    assert set(state.get('active_workers', {})) == set(c['adopted_active_task_ids'])
    completed = {x['task_id']: x for x in state['cells']}
    assert set(completed) == set(c['prior_terminal_task_ids'])
    active = {}
    for task_id, record in state['active_workers'].items():
        assert record['runner_sha256'] == c['runner_sha256']
        assert record['condition_sha256'] == c['prior_condition_sha256']
        assert not record['recovery_admission']
        cell = by_id[task_id]
        out = Path(cell['output_dir'])
        process = AdoptedProcess(record['pid'], runner, out)
        # A task may finish during the brief coordinator handoff; never relaunch it.
        if process.poll() is not None:
            assert (out / 'receipt.json').exists()
        active[task_id] = {'process':process, 'stdout':(out/'runner_stdout.json').open('a'),
                           'stderr':(out/'runner_stderr.log').open('a'), 'cell':cell, 'recovery':False}
    with (BATCH / 'FOUR_LANE_STARTED.json').open('x') as f:
        json.dump({'at':utcnow().isoformat(), 'condition_sha256':CONDITION_HASH,
                   'supervisor_sha256':digest(Path(__file__)), 'adopted_workers':state['active_workers']},f)
    state.update({'condition_sha256':CONDITION_HASH, 'max_concurrency':4})
    state['condition_lineage'] = list(dict.fromkeys(state.get('condition_lineage', []) + [c['prior_condition_sha256'],CONDITION_HASH]))
    state.pop('halt_reason',None)
    state.pop('current_task',None)
    need_recovery = False
    recovery_at = None
    hard_stop = None
    memory_wait_started = None
    env = os.environ.copy()
    env['GEMINI_API_KEY'] = Path.home().joinpath('keys/gemini_allen_key.txt').read_text().strip()
    while True:
        # Only this coordinator mutates the batch state; independent workers own their receipts.
        for task_id, job in list(active.items()):
            code = job['process'].poll()
            if code is None:
                continue
            job['stdout'].close(); job['stderr'].close()
            record, receipt, _ = terminal_record(job['cell'])
            record['recovery_admission'] = job['recovery']
            if code != 0:
                record['completion_class'] = 'unknown_infrastructure'
            assert task_id not in completed
            completed[task_id] = record
            del active[task_id]
            state['active_workers'].pop(task_id, None)
            kind = record['completion_class']
            if kind == 'unknown_infrastructure':
                hard_stop = 'Unknown infrastructure or accounting failure; preserve active tasks and stop new admissions'
            elif kind == 'service_failure':
                need_recovery = True
                failed_at = datetime.datetime.fromisoformat(receipt.get('finished_at', utcnow().isoformat()))
                proposed = failed_at + datetime.timedelta(minutes=30)
                recovery_at = max(recovery_at, proposed) if recovery_at else proposed
            elif job['recovery']:
                need_recovery = False
                recovery_at = None
            print(json.dumps({'event': 'cell_end', 'at': utcnow().isoformat(), **record}), flush=True)
        state['cells'] = sorted(completed.values(), key=lambda x: order[x['task_id']])
        state['accounted_usd'] = sum(x['accounted_usd'] for x in completed.values())
        state['global_accounted_usd'] = .7204245 + state['accounted_usd']
        state['active_reservations_usd'] = .75 * len(active)
        todo = pending_ids(index, completed, active)
        state['pending_task_ids'] = todo
        if state['global_accounted_usd'] + state['active_reservations_usd'] > 20 + 1e-9:
            hard_stop = 'Unexpected global accounting excess; stop new admissions'
        hold = ROOT / 'HOLD_NEXT_VALID_PI_CELL'
        if hold.exists():
            hard_stop = hold.read_text().strip()
        if not active and not todo:
            state['status'] = 'COMPLETED'
            state['finished_at'] = utcnow().isoformat()
            persist(state)
            return
        if hard_stop:
            state['status'] = 'DRAINING_ACTIVE_WORKERS' if active else 'STOPPED_INFRASTRUCTURE_REVIEW'
            state['halt_reason'] = hard_stop
            persist(state)
            if not active:
                return
            time.sleep(5)
            continue
        recovery_active = any(j['recovery'] for j in active.values())
        if need_recovery:
            state['status'] = 'DRAINING_FOR_PROVIDER_RECOVERY' if active else 'COOLDOWN_PROVIDER_RECOVERY'
            state['recovery_next_attempt_at'] = recovery_at.isoformat() if recovery_at else None
            cutoff = datetime.datetime.fromisoformat(c['admission_policy']['latest_recovery_admission_utc'])
            if not active and (state['additional_recovery_admissions'] >= 2 or max(utcnow(), recovery_at) > cutoff):
                state['status'] = 'HELD_PROVIDER_UNAVAILABLE'
                state['halt_reason'] = 'Bounded recovery exhausted or cutoff reached; untouched tasks remain pending provider availability'
                persist(state)
                return
            if active or utcnow() < recovery_at:
                persist(state)
                time.sleep(5)
                continue
        else:
            state['status'] = 'RUNNING'
            state.pop('recovery_next_attempt_at', None)
        # Recovery uses exactly one task. Healthy scheduling uses at most four.
        target = 1 if need_recovery or recovery_active else 4
        while todo and len(active) < target:
            assert digest(CONDITION) == CONDITION_HASH and digest(runner) == c['runner_sha256']
            assert digest(INDEX) == c['task_manifest_index_sha256']
            try:
                resources = resource_snapshot(c['docker_image'])
                available = resources['memory_available_bytes']
            except (ValueError, OSError, subprocess.SubprocessError):
                hard_stop = 'Resource probe failed; stop new admissions and preserve active tasks'
                break
            state['last_memory_available_bytes'] = available
            state['last_resource_snapshot'] = resources
            if not resource_admission_allowed(resources):
                memory_wait_started = memory_wait_started or time.monotonic()
                state['status'] = 'WAITING_FOR_RESOURCES'
                if not active and time.monotonic() - memory_wait_started > 900:
                    state['status'] = 'HELD_RESOURCE_PRESSURE'
                    state['halt_reason'] = 'CPU or memory admission threshold unmet for 15 minutes; no active tasks were interrupted'
                    persist(state)
                    return
                break
            memory_wait_started = None
            task_id = todo.pop(0)
            cell = by_id[task_id]
            assert digest(Path(cell['manifest'])) == cell['manifest_sha256']
            out = Path(cell['output_dir'])
            assert not (out / 'attempt_started.json').exists(), 'Never rerun an attempted task'
            assert reservation_ok(state['accounted_usd'], len(active)), 'Global full-cap admission reservation failed'
            out.mkdir(parents=True, exist_ok=True)
            stdout = (out / 'runner_stdout.json').open('x')
            stderr = (out / 'runner_stderr.log').open('x')
            command = [sys.executable, str(runner), 'run', '--input-dir', cell['input_dir'], '--manifest', cell['manifest'],
                       '--manifest-sha256', cell['manifest_sha256'], '--image', c['docker_image'], '--output-dir', str(out)]
            recovery = need_recovery
            if recovery:
                state['additional_recovery_admissions'] += 1
                state.setdefault('recovery_admission_history', []).append({'at': utcnow().isoformat(), 'task_id': task_id})
            proc = subprocess.Popen(command, stdout=stdout, stderr=stderr, env=env)
            active[task_id] = {'process': proc, 'stdout': stdout, 'stderr': stderr, 'cell': cell, 'recovery': recovery}
            state['active_workers'][task_id] = {'pid': proc.pid, 'started_at': utcnow().isoformat(), 'runner_sha256': c['runner_sha256'],
                                               'condition_sha256': CONDITION_HASH, 'reserved_usd': .75,
                                               'memory_available_at_admission_bytes': available, 'cpu_busy_fraction_at_admission': resources['cpu_busy_fraction'], 'recovery_admission': recovery}
            state['active_reservations_usd'] = .75 * len(active)
            state['pending_task_ids'] = pending_ids(index, completed, active)
            persist(state)
            print(json.dumps({'event': 'cell_start', 'at': utcnow().isoformat(), 'task_id': task_id, 'pid': proc.pid,
                              'active_count': len(active), 'recovery_admission': recovery}), flush=True)
            if recovery:
                break
        persist(state)
        time.sleep(5)

if __name__ == '__main__':
    main()
