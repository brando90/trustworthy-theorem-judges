"""TLDR: Trusted Lean callback for experiment 169 — compile one candidate proof term against the
immutable served context in an isolated sandbox, then accept only after independent kernel replay,
exact-type, standard-axiom and name-collision checks.

Acceptance rule (identical to scripts/natural_pipeline_preflight_v2.py): trusted kernel replay of
the candidate module via Environment.replay -> addDeclCore(doCheck := true), in a Lean process
whose LEAN_PATH excludes the candidate directory; exact structural type equality with the immutable
target; transitive axioms inside the standard allowlist; no name collision with the trusted
environment; and an unchanged candidate .olean hash. A proof-language guard runs first as a cheap
pre-filter and is never the sole gate.

The compiler environment carries no credential: every variable whose name matches a secret pattern
is removed before Lean starts, and candidate code never sees the service process environment.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import secrets
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = Path.home() / "veribench/veribench_dataset/lean_src"
PROOF_ONLY = Path.home() / "veribench-inf/experiments/13_tiny256_pi_prover_detection_false_alarm_11-04-2026/scripts/ProofOnly.lean"
REPLAY_SUPPORT = ROOT / "scripts/lean/KernelReplaySupport.lean"
REQUIRED_TOOLCHAIN = "leanprover/lean4:v4.22.0"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SECRET_PATTERN = re.compile(r"KEY|TOKEN|SECRET|PASSWORD|CREDENTIAL|AUTH|COOKIE|SESSION", re.I)
COMPILE_TIMEOUT_S = 420
MAX_PROOF_BYTES = 20000

# The guard is a deliberately narrow pre-filter: it blocks the constructs that would make a
# "successful" compile meaningless, and nothing else. A whitelist of identifiers would reject
# legitimate prover output, and the kernel replay — not this list — is the gate that decides.
FORBIDDEN_TOKENS = ("sorry", "admit", "sorryAx", "native_decide", "axiom", "run_tac", "set_option",
                    "macro", "macro_rules", "elab", "elab_rules", "unsafe", "partial", "import",
                    "opaque", "implemented_by", "extern", "init_quot", "addDecl", "skipKernelTC")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def clean_env() -> dict[str, str]:
    """Lean never sees a credential: drop every secret-shaped variable from the environment."""
    return {k: v for k, v in os.environ.items() if not SECRET_PATTERN.search(k)}


class ToolchainError(RuntimeError):
    pass


def toolchain_evidence() -> dict:
    """Record the actual installed Lean and Mathlib, refusing anything but the pinned toolchain."""
    pinned = (LEAN_PROJECT / "lean-toolchain").read_text().strip()
    if pinned != REQUIRED_TOOLCHAIN:
        raise ToolchainError(f"Lean project pins {pinned!r}, not {REQUIRED_TOOLCHAIN!r}")
    env = clean_env()
    lean = subprocess.check_output(["elan", "which", "lean"], cwd=LEAN_PROJECT, text=True, env=env).strip()
    version = subprocess.check_output([lean, "--version"], text=True, env=env).strip()
    if "4.22.0" not in version:
        raise ToolchainError(f"Resolved Lean is {version!r}, not 4.22.0")
    lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN_PROJECT,
                                        text=True, env=env).strip()
    manifest = json.loads((LEAN_PROJECT / "lake-manifest.json").read_text())
    packages = {p["name"]: {"rev": p.get("rev"), "inputRev": p.get("inputRev")}
                for p in manifest.get("packages", []) if p.get("name") in {"mathlib", "batteries"}}
    if "mathlib" not in packages:
        raise ToolchainError("No Mathlib package in the Lean project manifest")
    build = LEAN_PROJECT / ".lake/packages/mathlib/.lake/build/lib"
    if not build.is_dir():
        raise ToolchainError("Mathlib build artifacts are absent; the checker would rebuild them")
    return {"lean_binary": lean, "lean_version": version, "lean_toolchain": pinned,
            "mathlib": packages["mathlib"], "batteries": packages.get("batteries"),
            "mathlib_build_lib": str(build), "lean_path_entries": len(lean_path.split(":"))}


def guard(proof: str) -> list[str]:
    """Return the forbidden tokens this proof term uses; an empty list means the guard passed."""
    identifiers = set(re.findall(r"[A-Za-z_][A-Za-z_0-9.']*", proof))
    hit = {t for t in FORBIDDEN_TOKENS
           if t in identifiers or any(i.split(".")[-1] == t for i in identifiers)}
    return sorted(hit)


def _compile(lean: str, source: Path, lean_path: str, env: dict, *, output: bool = False,
             isolate: bool = False, extra: tuple[str, ...] = ()) -> tuple[int, str]:
    cmd = [lean, "-j1", "-DmaxHeartbeats=400000", *extra, "-R", str(source.parent)]
    if output:
        cmd += ["-o", str(source.with_suffix(".olean"))]
    cmd += [str(source)]
    if isolate and Path("/usr/bin/sandbox-exec").exists():
        # Candidate code runs with no network and may write only inside its own directory.
        # sandbox-exec matches resolved paths, so /var/... must become /private/var/... first.
        writable = os.path.realpath(source.parent)
        profile = ("(version 1)(allow default)(deny network*)(deny file-write*)"
                   "(allow file-write* (subpath " + json.dumps(writable) + "))")
        cmd = ["/usr/bin/sandbox-exec", "-p", profile] + cmd
    try:
        result = subprocess.run(cmd, cwd=LEAN_PROJECT, env=dict(env, LEAN_PATH=lean_path),
                                text=True, capture_output=True, timeout=COMPILE_TIMEOUT_S)
        return result.returncode, result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return 124, f"TIMEOUT_{COMPILE_TIMEOUT_S}s"


def _records(text: str, nonce: str) -> list[dict]:
    rows = []
    for line in text.splitlines():
        if "VB169_KERNEL_REPLAY_JSON " in line:
            try:
                row = json.loads(line.split("VB169_KERNEL_REPLAY_JSON ", 1)[1])
            except json.JSONDecodeError:
                continue
            if row.get("nonce") == nonce:
                rows.append(row)
    return rows


class TrustedChecker:
    """One prepared trusted environment per served control context."""

    def __init__(self, workspace: Path, context_source: str, target_name: str):
        self.workspace = workspace
        self.trusted = workspace / "trusted"
        self.trusted.mkdir(parents=True, exist_ok=True)
        os.chmod(self.trusted, 0o700)
        self.target_name = target_name
        self.evidence = toolchain_evidence()
        self.lean = self.evidence["lean_binary"]
        self.env = clean_env()
        self.lake_lean_path = subprocess.check_output(
            ["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN_PROJECT, text=True, env=self.env).strip()
        (self.trusted / "Context.lean").write_text(context_source)
        shutil.copyfile(PROOF_ONLY, self.trusted / "ProofOnly.lean")
        shutil.copyfile(REPLAY_SUPPORT, self.trusted / "KernelReplaySupport.lean")
        self.trusted_lean_path = f"{self.trusted}:{self.lake_lean_path}"
        self.build_log = {}
        for name in ("Context", "ProofOnly", "KernelReplaySupport"):
            code, text = _compile(self.lean, self.trusted / f"{name}.lean", self.trusted_lean_path,
                                  self.env, output=True)
            self.build_log[name] = {"exit_code": code, "tail": text[-800:] if code else ""}
            if code != 0:
                raise ToolchainError(f"Trusted module {name} failed to build: {text[-800:]}")
        # Protected context: any later change to these bytes invalidates every acceptance.
        self.protected = {p.name: sha(p.read_bytes()) for p in sorted(self.trusted.iterdir())
                          if p.suffix in {".lean", ".olean"}}

    def protected_intact(self) -> bool:
        return self.protected == {p.name: sha(p.read_bytes()) for p in sorted(self.trusted.iterdir())
                                  if p.suffix in {".lean", ".olean"}}

    def check(self, proof: str, *, target_name: str | None = None) -> dict:
        """Check one candidate proof term; returns a verdict record, never raising on a bad proof."""
        target = target_name or self.target_name
        verdict: dict = {"target": target, "accepted": False, "status": "unchecked",
                         "proof_sha256": sha(proof.encode()), "proof_bytes": len(proof.encode()),
                         "guard_rejected_tokens": [], "protected_context_intact_before": self.protected_intact()}
        if not verdict["protected_context_intact_before"]:
            verdict["status"] = "protected_context_modified"
            return verdict
        if not proof.strip():
            verdict["status"] = "empty_proof"
            return verdict
        if len(proof.encode()) > MAX_PROOF_BYTES:
            verdict["status"] = "proof_too_large"
            return verdict
        verdict["guard_rejected_tokens"] = guard(proof)
        if verdict["guard_rejected_tokens"]:
            verdict["status"] = "proof_language_rejected"
            return verdict

        case = Path(tempfile.mkdtemp(prefix="vb169_cand_", dir=self.workspace))
        os.chmod(case, 0o700)
        try:
            candidate = case / "Candidate.lean"
            source = ("import Context\nimport ProofOnly\n"
                      f"candidate claim : {target} := {json.dumps(proof, ensure_ascii=False)}\n")
            candidate.write_text(source)
            verdict["candidate_sha256"] = sha(source.encode())
            code, text = _compile(self.lean, candidate, f"{case}:{self.trusted_lean_path}", self.env,
                                  output=True, isolate=True)
            verdict["compile_exit_code"] = code
            verdict["compile_log_tail"] = text[-1200:]
            if code != 0:
                verdict["status"] = "compile_failed"
                return verdict
            olean = candidate.with_suffix(".olean")
            before = sha(olean.read_bytes())
            verdict["candidate_olean_sha256"] = before
            nonce = secrets.token_hex(24)
            replay = self.trusted / f"Replay_{nonce[:12]}.lean"
            replay.write_text("import Context\nimport KernelReplaySupport\n"
                              f'#vb_kernel_replay "{nonce}" {json.dumps(str(olean))} claim : {target}\n')
            try:
                # The candidate directory is deliberately absent from this LEAN_PATH.
                rcode, rtext = _compile(self.lean, replay, self.trusted_lean_path, self.env,
                                        extra=("-DElab.async=false",))
            finally:
                replay.unlink(missing_ok=True)
                (self.trusted / f"Replay_{nonce[:12]}.olean").unlink(missing_ok=True)
            rows = _records(rtext, nonce)
            verdict["kernel_replay"] = {"exit_code": rcode, "records": rows, "log_tail": rtext[-1200:]}
            verdict["candidate_olean_unchanged"] = sha(olean.read_bytes()) == before
            row = rows[0] if len(rows) == 1 else None
            verdict["axioms"] = row["axioms"] if row else None
            verdict["accepted"] = bool(
                rcode == 0 and row and row["name"] == "claim" and row["replayed"] and row["isTheorem"]
                and row["typeExact"] and not row["collisions"]
                and set(row["axioms"]) <= ALLOWED_AXIOMS and verdict["candidate_olean_unchanged"])
            verdict["status"] = "checked"
            verdict["protected_context_intact_after"] = self.protected_intact()
            if not verdict["protected_context_intact_after"]:
                verdict["accepted"] = False
                verdict["status"] = "protected_context_modified_during_check"
            return verdict
        finally:
            shutil.rmtree(case, ignore_errors=True)
