#!/usr/bin/env python3
"""Term-only certificate compilation, exact-goal kernel replay and axiom audit.

Trust boundary: the generated specifications, this wrapper, CertificateAudit.lean,
and the pinned Lean distribution are trusted. The proof channel accepts one term;
no .olean supplied by an untrusted party is imported. This is a bounded controlled
pilot checker, not a sandbox for arbitrary hostile Lean plugins or native code.
"""
import hashlib
import json
import os
import re
import secrets
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERSION = 'leanprover/lean4:v4.22.0'
DEFAULT_LEAN = Path.home() / '.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean'
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = {'sorry', 'admit', 'sorryAx', 'axiom', 'native_decide', 'run_tac',
             'run_elab', 'set_option', 'unsafe', 'partial', 'macro', 'elab',
             'initialize', 'import', 'opaque', 'implemented_by', 'extern',
             'addDecl', 'skipKernelTC', 'eval', 'compile', 'include_str'}
TARGETS = {'Coverage', 'Nonvacuous', 'Counterexample', 'Inconsistent'}
GOALS = '''
def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
'''


def sha(data):
    return hashlib.sha256(data.encode() if isinstance(data, str) else data).hexdigest()


def forbidden_tokens(proof):
    identifiers = re.findall(r"[A-Za-z_][A-Za-z_0-9.']*", proof)
    return sorted(set(identifiers) & FORBIDDEN | {x for x in FORBIDDEN if any(t.split('.')[-1] == x for t in identifiers)})


class CertificateChecker:
    def __init__(self, lean=None):
        self.lean = Path(lean or DEFAULT_LEAN).resolve()
        self.support = ROOT / 'lean/CertificateAudit.lean'
        self.env = {k: v for k, v in os.environ.items()
                    if not re.search('KEY|TOKEN|SECRET|PASSWORD|CREDENTIAL|AUTH|COOKIE|SESSION', k, re.I)}
        self.env.update({'LEAN_PATH': str(ROOT / 'lean'), 'OMP_NUM_THREADS': '1'})
        self.version = subprocess.check_output([str(self.lean), '--version'], text=True, env=self.env).strip()
        if 'version 4.22.0,' not in self.version:
            raise RuntimeError(f'Wrong Lean toolchain: {self.version}')
        if (ROOT / 'lean/lean-toolchain').read_text().strip() != VERSION:
            raise RuntimeError('Toolchain declaration does not match checker')
        build = self.compile(self.support, output=True)
        if build['exit_code'] != 0:
            raise RuntimeError(build['output'])
        self.pins = {
            'lean_toolchain': VERSION, 'lean_version': self.version,
            'lean_executable_sha256': sha(self.lean.read_bytes()),
            'lean_shared_library_sha256': sha((self.lean.parents[1] / 'lib/lean/libleanshared.so').read_bytes()),
            'checker_sha256': sha(Path(__file__).read_bytes()),
            'audit_source_sha256': sha(self.support.read_bytes()),
            'audit_olean_sha256': sha(self.support.with_suffix('.olean').read_bytes()),
            'kernel_environment_source_sha256': sha((self.lean.parents[1] / 'src/lean/Lean/Environment.lean').read_bytes()),
            'transitive_axioms_source_sha256': sha((self.lean.parents[1] / 'src/lean/Lean/Util/CollectAxioms.lean').read_bytes()),
        }

    def compile(self, path, output=False):
        argv = [str(self.lean), '-j1', '-DmaxHeartbeats=400000', '-DElab.async=false', '-DwarningAsError=false']
        if output:
            argv += ['-o', str(path.with_suffix('.olean'))]
        argv.append(str(path))
        try:
            result = subprocess.run(argv, cwd=ROOT / 'lean', env=self.env,
                                    capture_output=True, text=True, timeout=30)
            return {'exit_code': result.returncode, 'output': result.stdout + result.stderr,
                    'timeout_seconds': 30, 'threads': 1}
        except subprocess.TimeoutExpired as exc:
            return {'exit_code': 124, 'output': 'Certificate compilation timed out',
                    'timeout_seconds': 30, 'threads': 1}

    def check(self, statement, proofs, path, raw=None, audit_target=None, nonce=None, write=True):
        path = Path(path)
        path.parent.mkdir(parents=True, exist_ok=True)
        if not set(proofs) <= TARGETS:
            raise ValueError('Unknown target')
        for proof in proofs.values():
            if not isinstance(proof, str) or not 0 < len(proof.encode()) <= 20000:
                return {'accepted': False, 'status': 'invalid_proof_size'}
            if forbidden_tokens(proof):
                return {'accepted': False, 'status': 'proof_guard_rejected', 'tokens': forbidden_tokens(proof)}
        # Independent nonce binds accepted audit records to this specific invocation.
        nonce = nonce or secrets.token_hex(24)
        source = 'import CertificateAudit\n' + statement + GOALS
        audits = []
        if raw is None:
            for target, proof in proofs.items():
                claim = 'claim_' + target
                source += f'certificate {claim} : {target} := {json.dumps(proof)}\n'
                audits.append((claim, target))
        else:
            # Only adversarial deterministic tests use raw source; measured forecasts
            # are probabilities and never become executable Lean code.
            source += raw + '\n'
            audits = [('claim', audit_target or 'Coverage')]
        for claim, target in audits:
            source += f'#audit_certificate {json.dumps(nonce)} {claim} : {target}\n'
        if write:
            path.write_text(source)
        elif path.read_text() != source:
            raise ValueError(f'Saved certificate differs from reconstructed trusted source: {path.name}')
        compiled = self.compile(path)
        records = []
        for line in compiled['output'].splitlines():
            if 'TTJ07_CERTIFICATE_AUDIT ' in line:
                try:
                    row = json.loads(line.split('TTJ07_CERTIFICATE_AUDIT ', 1)[1])
                except json.JSONDecodeError:
                    continue
                if row.get('nonce') == nonce:
                    records.append(row)
        accepted = (compiled['exit_code'] == 0 and len(records) == len(audits)
                    and {r.get('claim') for r in records} == {a[0] for a in audits}
                    and all(r.get('exact_goal') is True and r.get('kernel_replayed') is True
                            and set(r.get('axioms', [])) <= AXIOMS for r in records))
        return {'accepted': accepted, 'status': 'accepted' if accepted else 'unresolved_timeout' if compiled['exit_code'] == 124 else 'certificate_rejected',
                'source_sha256': sha(source), 'statement_sha256': sha(statement),
                'targets': [a[1] for a in audits], 'audit_nonce': nonce,
                'audit_records': records, 'compile': compiled}
