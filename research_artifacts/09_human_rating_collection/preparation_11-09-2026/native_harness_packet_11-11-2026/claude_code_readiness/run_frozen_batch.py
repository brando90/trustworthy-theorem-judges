#!/usr/bin/env python3
"""One frozen serial admission per task; never retry an existing attempt."""
import datetime, fcntl, hashlib, json, os, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
REPO = Path('/Users/brandomiranda/trustworthy-theorem-judges')
RUNNER = REPO / 'experiments/09_human_rating_collection/support/scripts/native_packet_generation/claude_code_runner.py'
CONDITION = ROOT / 'CLAUDE_CODE_CONDITION.json'
MANIFEST = ROOT / 'inputs_and_existing/INPUT_MANIFEST.json'
OUTPUT = ROOT / 'claude_code_outputs'
EXPECTED = 'afcb028cbb65c339d4f1d041fafbcbca9d6f1502b9009528647a05bc6ff70de2'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(p, d):
    q=p.with_suffix('.tmp'); q.write_text(json.dumps(d,indent=2)+'\n');q.replace(p)
lock = (ROOT / 'claude_code_readiness/batch.lock').open('w')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
assert sha(CONDITION)==EXPECTED
c=json.loads(CONDITION.read_text())
assert sha(RUNNER)==c['runner_sha256']
assert sha(MANIFEST)==c['input_manifest_sha256']
assert len(c['task_order'])==25 and len(set(c['task_order']))==25
OUTPUT.mkdir(exist_ok=True)
ledger={'started_at':now(),'pid':os.getpid(),'condition_sha256':EXPECTED,'status':'RUNNING','tasks':{t:{'status':'PENDING'} for t in c['task_order']}}
ledger_path=ROOT/'claude_code_readiness/BATCH_STATUS.json'
save(ledger_path,ledger)
for task in c['task_order']:
    cell=OUTPUT/task; previous=cell/'receipt.json'
    if cell.exists():
        if previous.exists():
            prior=json.loads(previous.read_text())
            if prior.get('status')=='TERMINAL':
                ledger['tasks'][task]=prior
                continue
        ledger.update(status='BLOCKED_EXISTING_ATTEMPT',blocked_task=task,updated_at=now())
        save(ledger_path,ledger);sys.exit(2)
    assert sha(RUNNER)==c['runner_sha256'] and sha(CONDITION)==EXPECTED
    ledger['tasks'][task]={'status':'RUNNING','started_at':now()};save(ledger_path,ledger)
    args=[sys.executable,str(RUNNER),'run','--manifest',str(MANIFEST),'--condition',str(CONDITION),'--condition-sha256',EXPECTED,'--task-id',task,'--token-file','/Users/brandomiranda/keys/claude_personal_oauth_token.txt','--output-dir',str(OUTPUT)]
    print(now(),'ADMIT',task,flush=True)
    result=subprocess.run(args)
    receipt=json.loads(previous.read_text()) if previous.exists() else {'status':'NO_RECEIPT','runner_exit':result.returncode}
    ledger['tasks'][task]=receipt;ledger['updated_at']=now();save(ledger_path,ledger)
    print(now(),'TERMINAL',task,receipt.get('status'),receipt.get('stop_reason'),flush=True)
    native=receipt.get('native_result') or {}
    errors=json.dumps(native).lower()
    infra=(receipt.get('status')!='TERMINAL' or receipt.get('stop_reason')=='process_exit_without_result' or any(x in errors for x in ['authentication_error','invalid_api_key','oauth token','rate_limit_error','billing_error','credit balance','usage limit']))
    if infra or (receipt.get('actual_models') and not receipt.get('model_identity_verified')):
        ledger.update(status='BLOCKED_INFRASTRUCTURE_OR_IDENTITY',blocked_task=task,updated_at=now());save(ledger_path,ledger);sys.exit(3)
ledger.update(status='FULL_SET_TERMINAL',finished_at=now());save(ledger_path,ledger)
print(now(),'FULL_SET_TERMINAL',flush=True)
