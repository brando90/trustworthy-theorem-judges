#!/usr/bin/env python3
"""TLDR: Mechanical statement-only context exporter for the frozen 100-pair natural-output sample.

For every (gold task file, saved solver file) pair it namespace-wraps the two originals byte for
byte, compiles them with the pinned Lean toolchain, asks Lean itself (never a regular expression)
for the declaration list and the implementation dependencies, abstracts every implementation into a
universally quantified variable, inlines every proposition helper and nullary constant, and emits a
proof-free `Context.lean` holding only `AgentSpec`, `GoldSpec`, `Coverage`, `Nonvacuous` and the
leakage/vacuity controls.  Nothing from the original proofs reaches the exported context.

The exporter resolves a case only when every reference implementation has an agent definition of
exactly the same type.  Representation changes (the historical bridges' adapters) are reported as
unresolved with the exact reason; they are readings, not mechanical facts.

No model is called.  No original source byte is modified.
"""
from __future__ import annotations

import argparse
import concurrent.futures
from collections import Counter
import hashlib
import json
import os
import re
import secrets
import shutil
import subprocess
import sys
import time
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
EXPERIMENT = SCRIPTS.parents[1]
REPO = EXPERIMENT.parents[1]
LEAN_SUPPORT = SCRIPTS / "lean"
PROJECT = Path.home() / "veribench/veribench_dataset/lean_src"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.22.0"
SAMPLE_SHA = "0895f562f019e983e7aabad5ad871c0ed6ab81e673cd025dc129e03e59702b1e"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Interface-matching tiers.  `unique_type` and `name_within_type` are exact mechanical matches;
# `functional_imperative_convention` disambiguates two same-type definitions by the naming
# convention both files follow, which is a weaker, reported ground.
EXACT_RULES = {"unique_type", "name_within_type"}
CONVENTION_RULES = {"functional_imperative_convention"}
DECLARED_RULES = {"declared_adapter"}
ADAPTERS = SCRIPTS / "adapters"


CONTEXT_HEADER = (
    "/- Statement-only formal specification coverage context (case {id}).\n"
    "   `AgentSpec` is the conjunction of every statement the candidate file establishes about its\n"
    "   own implementation; `GoldSpec` is the conjunction of every statement the reference task\n"
    "   file requires of an implementation.  Every implementation is an arbitrary function\n"
    "   variable: no concrete definition and no proof from either source file is present here.\n"
    "   Targets: `Natural.Coverage` and `Natural.Nonvacuous`. -/\n"
)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_public_names(text: str) -> list[str]:
    """Named, non-private theorems in Lean source text.

    Vendored unchanged from veribench-inf experiment
    13_tiny256_pi_prover_detection_false_alarm_11-04-2026/scripts/lean_runner.py, and used here only
    as an independent audit of the declaration list Lean reports.
    """
    clean = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        pair = text[i:i + 2]
        c = text[i]
        if depth:
            if pair == '/-':
                depth += 1; i += 2; continue
            if pair == '-/':
                depth -= 1; i += 2; continue
            clean.append('\n' if c == '\n' else ' '); i += 1; continue
        if string:
            if c == '\\':
                i += 2; continue
            if c == '"':
                string = False
            clean.append('\n' if c == '\n' else ' '); i += 1; continue
        if pair == '/-':
            depth = 1; i += 2; continue
        if pair == '--':
            end = text.find('\n', i); i = len(text) if end < 0 else end; continue
        if c == "'":
            char = re.match(r"'(?:\\(?:u\{[^}]+\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'", text[i:])
            if char:
                clean.append(' '); i += len(char.group()); continue
        if c == '"':
            string = True; clean.append(' '); i += 1; continue
        clean.append(c); i += 1
    code = ''.join(clean)
    found = re.findall(
        r'(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:protected|noncomputable)\s+)?(?:theorem|lemma)\s+([^\s(:{\[]+)',
        code)
    return sorted(set(found))


def wrap(text: str, namespace: str) -> str:
    """Namespace-wrap an original file without altering any other byte (experiment 142 prep_wave)."""
    marks = list(re.finditer(r'(?m)^import \S+[ \t]*\n', text))
    end = marks[-1].end()
    return text[:end] + f'namespace {namespace}\n' + text[end:].rstrip() + f'\nend {namespace}\n'


class Toolchain:
    def __init__(self, project: Path):
        self.project = project
        toolchain = (project / 'lean-toolchain').read_text().strip()
        if toolchain != EXPECTED_TOOLCHAIN:
            raise SystemExit(f'pinned toolchain is {toolchain}, expected {EXPECTED_TOOLCHAIN}')
        self.toolchain = toolchain
        self.lean = subprocess.check_output(['elan', 'which', 'lean'], cwd=project, text=True).strip()
        self.lean_path = subprocess.check_output(
            ['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=project, text=True).strip().splitlines()[-1]
        self.version = subprocess.check_output([self.lean, '--version'], text=True).strip()
        self.lake_manifest_sha256 = sha((project / 'lake-manifest.json').read_bytes())
        # Never hand provider credentials to a Lean subprocess.
        self.env = {k: v for k, v in os.environ.items()
                    if not re.search(r'KEY|TOKEN|SECRET|PASSWORD|CREDENTIAL|AUTH', k, re.I)}

    def compile(self, source: Path, path_dirs: list[Path], olean: bool = False,
                timeout: int = 420) -> dict:
        cmd = [self.lean, '-j1', '-DmaxHeartbeats=400000', '-R', str(source.parent)]
        if olean:
            cmd += ['-o', str(source.with_suffix('.olean'))]
        cmd += [str(source)]
        lean_path = ':'.join([str(d) for d in path_dirs] + [self.lean_path])
        start = time.monotonic()
        try:
            done = subprocess.run(cmd, cwd=self.project, env=dict(self.env, LEAN_PATH=lean_path),
                                  capture_output=True, text=True, timeout=timeout)
            code, out = done.returncode, done.stdout + done.stderr
        except subprocess.TimeoutExpired as exc:
            code = 124
            out = ((exc.stdout or b'').decode(errors='replace') if isinstance(exc.stdout, bytes)
                   else (exc.stdout or '')) + f'\nTIMEOUT_{timeout}s\n'
        source.with_suffix('.log').write_text(out + f'\nexit {code}\n')
        return {'source': source.name, 'source_sha256': sha(source.read_bytes()), 'exit_code': code,
                'seconds': round(time.monotonic() - start, 2),
                'command': cmd, 'cwd': str(self.project), 'lean_path': lean_path,
                'timeout_seconds': timeout, 'output': out}


def axioms_of(text: str) -> dict[str, list[str]]:
    found = {}
    for name, axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S):
        found[name] = [x.strip() for x in axs.split(',') if x.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        found[name] = []
    return found


def probe_sources(arity: int) -> dict[str, tuple[str, bool]]:
    """Leakage, vacuity and shape controls, instantiated at this context's binder count.

    Each entry is (source, expected_to_compile).  `leak_gold_only` is the negative control: if the
    reference obligations follow for an arbitrary implementation, the case cannot discriminate a
    prover and is reported unresolved.
    """
    names = ' '.join(f'f{i}' for i in range(arity))
    intro = f'  intro {names}\n' if arity else ''
    leak = ('import Ctx\nset_option maxHeartbeats 400000\n'
            '/- Negative leakage control: these obligations must NOT follow for an arbitrary\n'
            '   implementation.  Compiling here is a defect in the exported context. -/\n'
            'theorem vb169_leak : Natural.LeakGoldOnly := by\n'
            '  unfold Natural.LeakGoldOnly Natural.GoldSpec\n'
            + intro +
            '  first\n    | trivial\n    | rfl\n    | decide\n    | norm_num\n    | omega\n'
            '    | simp_all\n    | aesop\n')
    vac_cov = ('import Ctx\nset_option maxHeartbeats 400000\n'
               '/- A vacuous implication is provable, which is why credit also needs the witness. -/\n'
               'theorem vb169_vacuous_coverage : Natural.VacuousCoverage := by\n'
               f'  intro {names} h\n  exact h.elim\n')
    vac_wit = ('import Ctx\nset_option maxHeartbeats 400000\n'
               '/- A witness for a false specification must not exist. -/\n'
               'theorem vb169_vacuous_witness : Natural.VacuousWitness := by\n'
               '  first\n    | trivial\n    | simp [Natural.VacuousWitness]\n    | decide\n'
               '    | aesop\n')
    shape = ('import Ctx\nset_option maxHeartbeats 400000\n'
             '/- Positive shape control: the exported targets elaborate as propositions. -/\n'
             'example : Prop := Natural.Coverage\nexample : Prop := Natural.Nonvacuous\n'
             'theorem vb169_identity : Natural.Coverage → Natural.Coverage := by exact id\n'
             '#print axioms vb169_identity\n')
    return {'shape': (shape, True), 'leak_gold_only': (leak, False),
            'vacuous_coverage': (vac_cov, True), 'vacuous_witness': (vac_wit, False)}


def witness_source(report: dict, adapter_text: str, nonce: str) -> str:
    """Instantiate the exported specifications back at the original definitions and round-trip them.

    This module imports the proof-bearing sources, so it never reaches a tested context.  It is the
    mechanical faithfulness check: `agent_satisfies` proves the exported candidate specification is
    satisfied by the candidate's own implementation (hence non-vacuous), `gold_instantiation` proves
    the exported reference specification is the reference file's own obligations, and
    `#vb169_roundtrip` re-derives both abstractions and compares them to what the exported file
    actually elaborates to.

    Under a declared representation adapter the reference specification is stated about the
    *candidate's* interface, so `gold_instantiation` is not available and is omitted; the round trip
    still applies.
    """
    gold_args = ' '.join(report['goldArgs'])
    agent_args = ' '.join(report['agentArgs'])
    gold_terms = ', '.join('@' + n for n in report['goldTheorems'])
    agent_terms = ', '.join('@' + n for n in report['agentTheorems'])
    slots = len(report['slots'])
    witness = ('⟨' + ', '.join(report['agentArgs'] + ['agent_satisfies']) + '⟩'
               if slots else 'agent_satisfies')
    declared = any(s['rule'] == 'declared_adapter' for s in report['slots'])
    body = (
        "import Gold\nimport Agent\nimport Ctx\nimport ExtractSupport\n"
        "set_option maxHeartbeats 1000000\n"
        "namespace VB169Witness\n\n"
        f"theorem agent_satisfies : Natural.AgentSpec {agent_args} :=\n"
        f"  ⟨{agent_terms}{', ' if agent_terms else ''}trivial⟩\n\n")
    if not declared:
        body += (f"theorem gold_instantiation : Natural.GoldSpec {gold_args} :=\n"
                 f"  ⟨{gold_terms}{', ' if gold_terms else ''}trivial⟩\n\n")
    body += (f"theorem nonvacuous : Natural.Nonvacuous := {witness}\n\n"
             "end VB169Witness\n"
             "#print axioms VB169Witness.agent_satisfies\n")
    if not declared:
        body += "#print axioms VB169Witness.gold_instantiation\n"
    body += ("#print axioms VB169Witness.nonvacuous\n"
             f"#vb169_roundtrip {json.dumps(nonce)} {json.dumps(adapter_text)}\n")
    return body


def static_context_checks(text: str) -> dict:
    """Deterministic checks that no proof, implementation or source identifier leaked."""
    imports = re.findall(r'(?m)^import (\S+)', text)
    body = text
    return {
        'imports': imports,
        'imports_only_mathlib': imports == ['Mathlib'],
        'no_gold_or_agent_identifier': ('Gold.' not in body) and ('Agent.' not in body),
        'no_theorem_declaration': not re.search(r'(?m)^\s*(theorem|lemma|example|instance)\b', body),
        'no_tactic_block': ':= by' not in body,
        'no_sorry': 'sorry' not in body,
        'no_native_decide': 'native_decide' not in body,
        'declares_all_targets': all(f'def {n} ' in body or f'def {n} :' in body for n in
                                    ['AgentSpec', 'GoldSpec', 'Coverage', 'Nonvacuous',
                                     'LeakGoldOnly', 'VacuousCoverage', 'VacuousWitness']),
    }


def git_blob(path: str, commit: str) -> bytes:
    return subprocess.check_output(['git', 'cat-file', 'blob', f'{commit}:{path}'], cwd=REPO)


def run_case(row: dict, tool: Toolchain, out_root: Path, commit: str, support: Path) -> dict:
    module = row['module']
    case = out_root / 'cases' / module
    build = case / 'build'
    build.mkdir(parents=True, exist_ok=True)
    receipt = {
        'id': row['id'], 'module': module, 'task': row['task'], 'solver': row['solver'],
        'category': row['category'], 'repo_commit': commit,
        'gold_path': row['gold_path'], 'gold_sha256': row['gold_current_head_sha256'],
        'solver_path': row['source_path'], 'solver_sha256': row['source_sha256'],
        'lean_version': tool.version, 'lean_toolchain': tool.toolchain,
        'lake_manifest_sha256': tool.lake_manifest_sha256,
        'extractor_sha256': sha((support / 'ExtractSupport.lean').read_bytes()),
        'driver_sha256': sha(Path(__file__).read_bytes()),
        'status': 'unresolved', 'reasons': [], 'compiles': [],
    }
    gold_bytes = git_blob(row['gold_path'], commit)
    solver_bytes = git_blob(row['source_path'], commit)
    receipt['gold_sha256_verified'] = sha(gold_bytes) == row['gold_current_head_sha256']
    receipt['solver_sha256_verified'] = sha(solver_bytes) == row['source_sha256']
    if not (receipt['gold_sha256_verified'] and receipt['solver_sha256_verified']):
        receipt['reasons'].append('source hash mismatch against the frozen inventory')
        return finish(receipt, case)
    gold_text, solver_text = gold_bytes.decode(), solver_bytes.decode()
    receipt['gold_source_theorem_names'] = source_public_names(gold_text)
    receipt['agent_source_theorem_names'] = source_public_names(solver_text)
    (build / 'Gold.lean').write_text(wrap(gold_text, 'Gold'))
    (build / 'Agent.lean').write_text(wrap(solver_text, 'Agent'))
    receipt['wrapped_gold_sha256'] = sha((build / 'Gold.lean').read_bytes())
    receipt['wrapped_agent_sha256'] = sha((build / 'Agent.lean').read_bytes())

    build_path = [build, support]
    for name in ('Gold', 'Agent'):
        result = tool.compile(build / f'{name}.lean', build_path, olean=True)
        receipt['compiles'].append({k: v for k, v in result.items() if k != 'output'})
        if result['exit_code'] != 0:
            receipt['reasons'].append(
                f'{name} source does not compile in this project: exit {result["exit_code"]}; '
                + last_error(result['output']))
            return finish(receipt, case)

    header = CONTEXT_HEADER.format(id=row['id'])
    adapter_file = ADAPTERS / f'{module}.json'
    adapter_text = adapter_file.read_text() if adapter_file.exists() else ''
    if adapter_text:
        declaration = json.loads(adapter_text)
        receipt['declared_adapter'] = {
            'file': str(adapter_file.relative_to(EXPERIMENT)),
            'sha256': sha(adapter_file.read_bytes()),
            'reading_record': declaration.get('reading_record'),
            'independently_read': bool(
                (declaration.get('reading_record') or {}).get('independent_reading_recorded')),
            'pairs': declaration.get('pairs'),
        }
    # One compile derives both printings of the same abstraction: the readable one, and the fully
    # explicit one used when the readable form does not re-elaborate to the same expression.
    nonces = {mode: secrets.token_hex(16) for mode in ('implicit', 'explicit')}
    (build / 'Extract.lean').write_text(
        'import ExtractSupport\nimport Gold\nimport Agent\n' + ''.join(
            f'#vb169_extract {json.dumps(nonces[mode])} {json.dumps(header)} '
            f'{json.dumps(adapter_text)} {json.dumps(mode)}\n' for mode in nonces))
    result = tool.compile(build / 'Extract.lean', build_path, timeout=600)
    receipt['compiles'].append({k: v for k, v in result.items() if k != 'output'})
    reports: dict[str, dict] = {}
    for line in result['output'].splitlines():
        if 'VB169_EXTRACT_JSON ' in line:
            try:
                candidate = json.loads(line.split('VB169_EXTRACT_JSON ', 1)[1])
            except json.JSONDecodeError:
                continue
            for mode, nonce in nonces.items():
                if candidate.get('nonce') == nonce:
                    reports[mode] = candidate
    if 'implicit' not in reports:
        receipt['reasons'].append(
            f'extraction did not produce a report: exit {result["exit_code"]}; '
            + last_error(result['output']))
        return finish(receipt, case)
    report = reports['implicit']
    receipt['extraction'] = {k: v for k, v in report.items() if k != 'contextSource'}
    receipt['slot_rules'] = sorted({s['rule'] for s in report['slots']})
    receipt['match_tier'] = tier_of(report)
    # Independent audit: the declaration list Lean reports against a text scan of the sources.
    # Both sides are compared on the final name component, since the text scan sees the name as
    # written inside its namespace while Lean reports the fully qualified name.
    def short(names):
        # The text scan cannot see namespaces and reports each short name once, so the audit
        # compares the *sets* of final name components and records the counts separately.
        return {n.split('.')[-1] for n in names}
    receipt['lean_vs_source_names_agree'] = {
        'gold': short(report['goldTheorems']) == short(receipt['gold_source_theorem_names']),
        'agent': short(report['agentTheorems']) == short(receipt['agent_source_theorem_names']),
        'gold_counts': [len(report['goldTheorems']), len(receipt['gold_source_theorem_names'])],
        'agent_counts': [len(report['agentTheorems']), len(receipt['agent_source_theorem_names'])],
        'gold_only_in_lean': sorted(short(report['goldTheorems'])
                                    - short(receipt['gold_source_theorem_names'])),
        'gold_only_in_text': sorted(short(receipt['gold_source_theorem_names'])
                                    - short(report['goldTheorems'])),
        'agent_only_in_lean': sorted(short(report['agentTheorems'])
                                     - short(receipt['agent_source_theorem_names'])),
        'agent_only_in_text': sorted(short(receipt['agent_source_theorem_names'])
                                     - short(report['agentTheorems']))}
    if not report['ok']:
        receipt['reasons'].extend(report['reasons'])
        return finish(receipt, case)

    attempts = []
    accepted = None
    for mode in ('implicit', 'explicit'):
        if mode not in reports:
            continue
        attempt = verify_context(reports[mode], mode, case, build, support, tool, adapter_text)
        attempts.append(attempt)
        if attempt['accepted']:
            accepted = attempt
            break
    receipt['print_attempts'] = [{k: v for k, v in a.items() if k != 'context_source'}
                                 for a in attempts]
    chosen = accepted or attempts[-1]
    receipt['pp_mode'] = chosen['pp_mode']
    receipt['context_path'] = chosen['context_path']
    receipt['context_sha256'] = chosen['context_sha256']
    receipt['context_static_checks'] = chosen['static_checks']
    receipt['context_compiles'] = chosen['context_compiles']
    receipt['roundtrip'] = chosen['roundtrip']
    receipt['witness'] = chosen['witness']
    receipt['controls'] = chosen.get('controls')
    receipt['controls_all_as_expected'] = chosen.get('controls_all_as_expected')
    receipt['compiles'].extend(chosen['compiles'])
    if accepted is None:
        receipt['reasons'].extend(chosen['reasons'])
        return finish(receipt, case)
    (case / 'Context.lean').write_text(chosen['context_source'])
    receipt['status'] = 'emitted'
    return finish(receipt, case)


def verify_context(report: dict, mode: str, case: Path, build: Path, support: Path,
                   tool: Toolchain, adapter_text: str) -> dict:
    """Compile one printing of the exported context and run every check against it."""
    ctx = case / f'ctx_{mode}'
    probes = case / f'probes_{mode}'
    for d in (ctx, probes):
        d.mkdir(parents=True, exist_ok=True)
    out = {'pp_mode': mode, 'accepted': False, 'reasons': [], 'compiles': [],
           'context_source': report['contextSource'],
           'context_path': str((ctx / 'Ctx.lean').relative_to(case)),
           'context_sha256': sha(report['contextSource'].encode()),
           'static_checks': static_context_checks(report['contextSource']),
           'context_compiles': False, 'roundtrip': None, 'witness': None}
    (ctx / 'Ctx.lean').write_text(report['contextSource'])
    # The tested environment sees only Mathlib and the exported context.
    result = tool.compile(ctx / 'Ctx.lean', [ctx], olean=True, timeout=420)
    out['compiles'].append({k: v for k, v in result.items() if k != 'output'})
    out['context_compiles'] = result['exit_code'] == 0
    if not out['context_compiles']:
        out['reasons'].append(f'exported context ({mode} printing) does not compile: '
                              + last_error(result['output']))
        return out

    witness_nonce = secrets.token_hex(16)
    witness_file = build / f'Witness_{mode}.lean'
    witness_file.write_text(witness_source(report, adapter_text, witness_nonce))
    result = tool.compile(witness_file, [build, ctx, support], timeout=600)
    out['compiles'].append({k: v for k, v in result.items() if k != 'output'})
    witness_axioms = axioms_of(result['output'])
    declared = any(s['rule'] == 'declared_adapter' for s in report['slots'])
    roundtrip = None
    for line in result['output'].splitlines():
        if 'VB169_ROUNDTRIP_JSON ' in line:
            try:
                candidate = json.loads(line.split('VB169_ROUNDTRIP_JSON ', 1)[1])
            except json.JSONDecodeError:
                continue
            if candidate.get('nonce') == witness_nonce:
                roundtrip = candidate
    out['roundtrip'] = ({'ok': roundtrip['ok'], 'status': roundtrip['status'],
                         'detail': roundtrip['ppMode'], 'reasons': roundtrip['reasons']}
                        if roundtrip else {'ok': False, 'status': 'not_reported', 'detail': '',
                                           'reasons': ['no round-trip record']})
    out['witness'] = {
        'exit_code': result['exit_code'], 'axioms': witness_axioms,
        'agent_specification_satisfied': result['exit_code'] == 0
            and 'VB169Witness.agent_satisfies' in witness_axioms,
        'gold_specification_instantiates': (
            'not_applicable_under_declared_adapter' if declared else
            (result['exit_code'] == 0 and 'VB169Witness.gold_instantiation' in witness_axioms)),
        'nonvacuity_witnessed': result['exit_code'] == 0
            and 'VB169Witness.nonvacuous' in witness_axioms,
        'axioms_outside_allowlist': sorted(
            {a for axs in witness_axioms.values() for a in axs} - ALLOWED_AXIOMS),
    }
    if result['exit_code'] != 0:
        out['reasons'].append(
            f'the exported specifications ({mode} printing) do not instantiate back at the '
            'original definitions: ' + last_error(result['output']))
        return out
    if not out['roundtrip']['ok']:
        out['reasons'].append(f'pretty-print round trip failed ({mode} printing): '
                              + '; '.join(out['roundtrip']['reasons']))
        return out

    controls = {}
    for name, (text, expected_zero) in probe_sources(len(report['slots'])).items():
        path = probes / f'Probe_{name}.lean'
        path.write_text(text)
        result = tool.compile(path, [ctx], timeout=240)
        out['compiles'].append({k: v for k, v in result.items() if k != 'output'})
        controls[name] = {'exit_code': result['exit_code'], 'expected_provable': expected_zero,
                          'provable': result['exit_code'] == 0,
                          'timed_out': result['exit_code'] == 124,
                          'tactic_budget_seconds': 240,
                          'as_expected': (result['exit_code'] == 0) == expected_zero}
    out['controls'] = controls
    out['controls_all_as_expected'] = all(c['as_expected'] for c in controls.values())
    if not controls['leak_gold_only']['as_expected']:
        out['reasons'].append(
            'leakage control failed: the reference obligations are provable for an arbitrary '
            'implementation, so this context cannot discriminate a prover')
    if not controls['vacuous_witness']['as_expected']:
        out['reasons'].append('vacuity control failed: a witness for `False` was accepted')
    if not controls['shape']['as_expected']:
        out['reasons'].append('shape control failed: the exported targets do not elaborate')
    static_ok = all(v for v in out['static_checks'].values() if isinstance(v, bool))
    if not static_ok:
        out['reasons'].append('static context checks failed: ' + json.dumps(out['static_checks']))
    gold_ok = out['witness']['gold_specification_instantiates']
    out['accepted'] = bool(static_ok and out['controls_all_as_expected'] and out['roundtrip']['ok']
                           and out['witness']['agent_specification_satisfied']
                           and gold_ok in (True, 'not_applicable_under_declared_adapter'))
    return out


def tier_of(report: dict) -> str:
    rules = {s['rule'] for s in report['slots'] if s['gold']}
    if not report['ok']:
        return 'unresolved'
    if rules & DECLARED_RULES:
        return 'declared_adapter'
    if rules <= EXACT_RULES:
        return 'exact_interface'
    if rules <= EXACT_RULES | CONVENTION_RULES:
        return 'convention_disambiguated'
    return 'unresolved'


def last_error(output: str) -> str:
    """First compiler error line, else the last non-empty output line."""
    errors = [l for l in output.splitlines() if 'error' in l.lower()]
    if errors:
        return errors[0].strip()[:400]
    rest = [l for l in output.splitlines() if l.strip()]
    return (rest[-1].strip()[:400] if rest else '')


def finish(receipt: dict, case: Path) -> dict:
    (case / 'receipt.json').write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n')
    return receipt


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default=str(EXPERIMENT / 'results/natural_contexts'))
    ap.add_argument('--workers', type=int, default=6)
    ap.add_argument('--limit', type=int, default=0, help='run only the first N cases (development)')
    ap.add_argument('--only', default='', help='comma-separated module ids')
    args = ap.parse_args()

    out_root = Path(args.out).resolve()  # Lean runs with cwd set to the Mathlib project
    (out_root / 'cases').mkdir(parents=True, exist_ok=True)
    support = out_root / 'support'
    support.mkdir(exist_ok=True)
    shutil.copy2(LEAN_SUPPORT / 'ExtractSupport.lean', support / 'ExtractSupport.lean')

    sample = json.loads((EXPERIMENT / 'inputs/sample.json').read_text())
    if sha((EXPERIMENT / 'inputs/sample.json').read_bytes()) != SAMPLE_SHA:
        raise SystemExit('frozen sample manifest hash changed; refusing to run')
    inventory = json.loads((EXPERIMENT / 'results/reference_inventory.json').read_text())
    by_id = {r['id']: r for r in inventory['rows']}
    rows = [dict(by_id[r['id']]) for r in sample['rows']]
    assert len(rows) == 100 and len({r['module'] for r in rows}) == 100
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip()

    tool = Toolchain(PROJECT)
    result = tool.compile(support / 'ExtractSupport.lean', [support], olean=True, timeout=900)
    if result['exit_code'] != 0:
        print(result['output'][-3000:])
        raise SystemExit('the extractor does not compile')

    if args.only:
        wanted = set(args.only.split(','))
        rows = [r for r in rows if r['module'] in wanted]
    elif args.limit:
        rows = rows[:args.limit]

    started = time.time()
    results: list[dict] = []
    (out_root / 'run_state.json').write_text(json.dumps(
        {'status': 'RUNNING', 'attempted_denominator': len(rows), 'completed': 0,
         'started_unix': started, 'repo_commit': commit, 'lean_version': tool.version,
         'extractor_sha256': sha((support / 'ExtractSupport.lean').read_bytes()),
         'model_calls': 0}, indent=2) + '\n')
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_case, r, tool, out_root, commit, support): r for r in rows}
        for future in concurrent.futures.as_completed(futures):
            row = futures[future]
            try:
                results.append(future.result())
            except Exception as exc:  # a driver fault must stay visible, never silently drop a case
                results.append({'id': row['id'], 'module': row['module'], 'task': row['task'],
                                'solver': row['solver'], 'category': row['category'],
                                'status': 'driver_error', 'reasons': [f'{type(exc).__name__}: {exc}']})
            done = len(results)
            (out_root / 'run_state.json').write_text(json.dumps(
                {'status': 'RUNNING', 'attempted_denominator': len(rows), 'completed': done,
                 'emitted_so_far': sum(1 for x in results if x['status'] == 'emitted'),
                 'elapsed_seconds': round(time.time() - started, 1),
                 'repo_commit': commit, 'lean_version': tool.version, 'model_calls': 0},
                indent=2) + '\n')
            print(f'{done}/{len(rows)} {row["module"]} {results[-1]["status"]}', flush=True)

    results.sort(key=lambda r: r['module'])
    (out_root / 'full100_ledger.json').write_text(
        json.dumps({'rows': results}, indent=2, ensure_ascii=False) + '\n')
    summary = summarize(results, rows, tool, commit, started, support)
    (out_root / 'summary.json').write_text(json.dumps(summary, indent=2, ensure_ascii=False) + '\n')
    (out_root / 'run_state.json').write_text(json.dumps(
        {**summary, 'status': 'COMPLETE'}, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'unresolved_reason_counts'}, indent=2))
    return 0


def summarize(results, rows, tool, commit, started, support) -> dict:
    counts: dict[str, int] = {}
    for r in results:
        counts[r['status']] = counts.get(r['status'], 0) + 1
    reason_counts: dict[str, int] = {}
    for r in results:
        if r['status'] == 'emitted':
            continue
        for reason in (r.get('reasons') or ['no reason recorded']):
            key = re.sub(r'\s+', ' ', reason)[:160]
            reason_counts[key] = reason_counts.get(key, 0) + 1
    tiers: dict[str, int] = {}
    for r in results:
        tiers[r.get('match_tier', 'n/a')] = tiers.get(r.get('match_tier', 'n/a'), 0) + 1
    return {
        'condition': 'deterministic_statement_only_context_extraction_no_model_calls',
        'model': None, 'thinking': None, 'model_calls': 0,
        'invocation': ' '.join([sys.executable.split('/')[-1]] + sys.argv),
        'compile_command_template': (
            '<lean> -j1 -DmaxHeartbeats=400000 -R <source dir> [-o <olean>] <source file>, '
            'run with cwd=<Mathlib project> and LEAN_PATH=<case dirs>:<project LEAN_PATH>; the '
            'exact argv, cwd, LEAN_PATH and timeout of every compile are in each '
            "receipt's `compiles` list"),
        'lean_binary': tool.lean,
        'attempted': len(rows), 'attempted_denominator': 100,
        'status_counts': counts,
        'emitted': counts.get('emitted', 0),
        'unresolved': sum(v for k, v in counts.items() if k != 'emitted'),
        'match_tier_counts': tiers,
        'emitted_without_declared_adapter': sum(
            1 for r in results
            if r['status'] == 'emitted' and r.get('match_tier') != 'declared_adapter'),
        'emitted_with_declared_adapter_pending_independent_reading': sorted(
            r['module'] for r in results
            if r['status'] == 'emitted' and r.get('match_tier') == 'declared_adapter'),
        'contexts_compiled': sum(1 for r in results if r.get('context_compiles')),
        'nonvacuity_witnessed': sum(1 for r in results
                                    if (r.get('witness') or {}).get('nonvacuity_witnessed')),
        'gold_instantiation_checked': sum(
            1 for r in results
            if (r.get('witness') or {}).get('gold_specification_instantiates') is True),
        'roundtrip_exact': sum(1 for r in results if (r.get('roundtrip') or {}).get('ok')),
        'print_mode_counts': dict(Counter(r.get('pp_mode') for r in results
                                          if r['status'] == 'emitted')),
        'leakage_control_passed': sum(
            1 for r in results if ((r.get('controls') or {}).get('leak_gold_only') or {}).get('as_expected')),
        'leakage_control_failed': sorted(
            r['module'] for r in results
            if (r.get('controls') or {}).get('leak_gold_only')
            and not r['controls']['leak_gold_only']['as_expected']),
        'lean_vs_source_name_disagreements': sorted(
            r['module'] for r in results
            if r.get('lean_vs_source_names_agree')
            and not (r['lean_vs_source_names_agree']['gold']
                     and r['lean_vs_source_names_agree']['agent'])),
        'unresolved_reason_counts': dict(sorted(reason_counts.items(), key=lambda x: -x[1])),
        'repo_commit': commit, 'lean_version': tool.version, 'lean_toolchain': tool.toolchain,
        'lake_manifest_sha256': tool.lake_manifest_sha256,
        'extractor_sha256': sha((support / 'ExtractSupport.lean').read_bytes()),
        'driver_sha256': sha(Path(__file__).read_bytes()),
        'sample_sha256': SAMPLE_SHA,
        'wall_seconds': round(time.time() - started, 1),
        'claims_not_made': [
            'No natural-output prover detection or false-alarm rate is measured here.',
            'No reference truth (coverage or non-coverage) is established for any case.',
            'Type checking an exported context does not establish that it faithfully represents the '
            'natural-language meaning of either source file.',
        ],
    }


if __name__ == '__main__':
    sys.exit(main())
