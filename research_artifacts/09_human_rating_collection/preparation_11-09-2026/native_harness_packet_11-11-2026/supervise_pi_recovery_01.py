#!/usr/bin/env python3
from pathlib import Path
import subprocess,time,json,hashlib,datetime,sys
ROOT=Path(__file__).resolve().parent
POLICY=ROOT/'PI_ADMISSION_RECOVERY_01.json'
assert hashlib.sha256(POLICY.read_bytes()).hexdigest()=='793ea7bda9b81b443a00e803c3d56596585d2eac44f329b8ba54de7960d0d331'
p=json.loads(POLICY.read_text());driver=Path(p['driver'])
assert hashlib.sha256(driver.read_bytes()).hexdigest()==p['driver_sha256']
while subprocess.run(['tmux','has-session','-t','pi-ttj-native-valid-packet-gemini38flash-v6-11-11-2026'],capture_output=True).returncode==0:
    time.sleep(10)
s=json.loads((ROOT/'runs/pi_valid_v3/BATCH_STATUS.json').read_text())
assert len(s['cells'])==6 and s['status']=='HELD_BEFORE_NEXT_ADMISSION',s['status']
s['recovery_next_attempt_at']=p['next_attempt_not_before'];s['recovery_policy']='PI_ADMISSION_RECOVERY_01.json'
(ROOT/'runs/pi_valid_v3/BATCH_STATUS.json').write_text(json.dumps(s,indent=2,sort_keys=True)+'\n')
due=datetime.datetime.fromisoformat(p['next_attempt_not_before'])
while True:
    remaining=(due-datetime.datetime.now(datetime.timezone.utc)).total_seconds()
    if remaining<=0:break
    time.sleep(min(30,remaining))
hold=ROOT/'HOLD_NEXT_VALID_PI_CELL'
assert hold.read_text()=='Hold new admissions after active cell: repeated provider failures; bounded30minute recovery cooldown before one untouched task, then reassess.\n'
hold.unlink()
print(json.dumps({'event':'recovery_01_admission','at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'maximum_new_cells':1}),flush=True)
raise SystemExit(subprocess.run([sys.executable,str(driver)]).returncode)
