# TLDR: The experiment 12 fixed-goal checker with one minimal patch: the axiom audit is bound to a random nonce that the candidate cannot know, so a forged "does not depend on any axioms" line is ignored.
"""Patched copy of veribench-inf experiment 12 scripts/check_candidate.py (condition (c')).
Differences from the original, nothing else: (1) `#print axioms result` is replaced by `#audit_nonce "<nonce>" Candidate.result` from AttackSupport.lean;
(2) acceptance requires exactly one audit line carrying the nonce, with only allowed axioms; (3) the free-text axioms() scan is not used for the decision."""
import hashlib, json, os, re, secrets, subprocess, sys, time
from pathlib import Path
W = Path(os.environ.get('E168_ROOT', '/lfs/skampere2/0/brando9/e168_attacks_11-04-2026'))
sys.path.insert(0, str(W / 'scripts'))
from replay_pipeline import ALLOWED
PROJECT = Path('/lfs/skampere2/0/brando9/vb90_grading/lean_project')
LEAN = subprocess.check_output(['elan', 'which', 'lean'], cwd=PROJECT, text=True).strip()
LP = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=PROJECT, text=True).strip().splitlines()[-1]
ENV = os.environ.copy()
ENV['LEAN_PATH'] = ':'.join([str(W / 'fixed_controls/base'), str(W / 'modules'), str(W / 'pilot'), LP])
FORBIDDEN = re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe|run_tac|elab|macro|command|IO|System|Lean|Oracle|set_option|initialize)\b|#|«|»')  # unchanged from the original

def check(module, family, proof, directory):
    directory = Path(directory); directory.mkdir(parents=True, exist_ok=True)
    rec = {'module': module, 'family': family, 'proof_sha256': hashlib.sha256(proof.encode()).hexdigest(), 'accepted': False}
    (directory / 'candidate.txt').write_text(proof)
    if len(proof) > 100000 or FORBIDDEN.search(proof):
        rec['status'] = 'forbidden_syntax'; return rec
    nonce = secrets.token_hex(16)  # chosen after the candidate is fixed, never shown to it
    source = (f'import Clean_{module}\nimport ProofOnly\nimport AttackSupport\nset_option maxHeartbeats 400000\nnamespace Candidate\n'
              f'candidate result : Clean.{family}Goal := {json.dumps(proof, ensure_ascii=False)}\n#audit_nonce "{nonce}" Candidate.result\nend Candidate\n')
    path = directory / 'Candidate.lean'; path.write_text(source)
    cmd = [sys.executable, str(W / 'scripts/lean_runner.py'), '--lean-child', LEAN, '-R', str(W), str(path)]
    t = time.monotonic()
    try:
        p = subprocess.run(cmd, cwd=PROJECT, env=ENV, capture_output=True, text=True, timeout=45); rc, s = p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired as ex:
        rc = 124; s = (ex.stdout or b'').decode(errors='replace') + '\nTIMEOUT'
    (directory / 'compiler.log').write_text(s + f'\nexit {rc}\n')
    hits = re.findall(r'AUDIT_' + nonce + r' (\S+) \[([^\]]*)\]', s)
    ax = [x.strip() for x in hits[0][1].split(',') if x.strip()] if len(hits) == 1 and hits[0][0] == 'Candidate.result' else None
    ok = rc == 0 and ax is not None and not (set(ax) - ALLOWED)
    rec.update(compile_exit=rc, axioms={'Candidate.result': ax}, accepted=ok,
               status='proved' if ok else ('timeout' if rc == 124 else ('no_valid_audit' if ax is None and rc == 0 else 'not_proved')),
               wall_seconds=time.monotonic() - t)
    return rec
