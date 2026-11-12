#!/usr/bin/env python3
from pathlib import Path
import subprocess, time, json, hashlib, sys
ROOT=Path(__file__).resolve().parent
BATCH=ROOT/'runs/pi_valid_v3'
OLD_SESSION='pi-ttj-native-valid-packet-gemini38flash-v5-11-11-2026'
DRIVER=ROOT/'run_pi_valid_remaining_v5_accounting.py'
EXPECTED='1c9f5ebf2d21b9c9ac1dc0207e57d8abd84b2d26fb583f3f48862cfafb00adca'
assert hashlib.sha256(DRIVER.read_bytes()).hexdigest()==EXPECTED
for _ in range(210):
    if subprocess.run(['tmux','has-session','-t',OLD_SESSION],capture_output=True).returncode!=0:
        break
    time.sleep(10)
else:
    raise RuntimeError('Prior driver did not terminate within35minutes')
s=json.loads((BATCH/'BATCH_STATUS.json').read_text())
for cell in s['cells']:
    rp=Path(cell['receipt']); lp=rp.with_name('gateway_ledger.json')
    receipt=json.loads(rp.read_text()) if rp.exists() else {}
    ledger=json.loads(lp.read_text()) if lp.exists() else {}
    if 'accounted_usd' not in receipt or 'accounted_usd' not in ledger:
        cell['accounted_usd']=.75
        cell['accounting_missing']=True
        s['accounted_usd']=sum(c['accounted_usd'] for c in s['cells'])
        s['global_accounted_usd']=.7204245+s['accounted_usd']
        s['status']='STOPPED_INFRASTRUCTURE_REVIEW'
        s['halt_reason']='Missing accounting: full0.75reserved; investigate'
        (BATCH/'BATCH_STATUS.json').write_text(json.dumps(s,indent=2,sort_keys=True)+'\n')
        sys.exit(2)
assert s['status']=='HELD_BEFORE_NEXT_ADMISSION',s['status']
assert len(s['cells'])==4,len(s['cells'])
hold=ROOT/'HOLD_NEXT_VALID_PI_CELL'
assert hold.read_text()=='Pause after current cell to activate reviewed conservative missing-accounting guard; preserve current attempt.\n'
hold.unlink()
print('Verified prior four costs; activating reviewed accounting driver.',flush=True)
raise SystemExit(subprocess.run([sys.executable,str(DRIVER)]).returncode)
