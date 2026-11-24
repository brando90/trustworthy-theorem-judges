"""Generate the alternative references G'x (x = gpt via Codex, claude via Claude Code) and the half-coverage file H for experiment 24, with the compile gate and the statement-change gate.

Use: on skampere1, from the experiment folder: python3 scripts/gen_alt.py --kind alt --family codex|claude  or  --kind half  [--tasks T28,T40] [--par 6].
Needs python3, scripts/llm.py, the router, and Lean in the VeriBench environment (LEAN_SRC below). Writes materials/<task>/Gprime_<family>.lean or H.lean plus materials/<task>/<name>.gen.json (attempts, lane, gate result). Cached: an accepted file is never regenerated.
Example: python3 scripts/gen_alt.py --kind alt --family codex --par 6
"""
import argparse, json, os, re, subprocess, sys, concurrent.futures as cf, pathlib, time
sys.path.insert(0, os.path.dirname(__file__))
import llm
from lean_utils import replace_proofs, similarity, statements, theorem_names, strip_comments
HERE = pathlib.Path(__file__).resolve().parents[1]
LEAN_SRC = '/lfs/skampere1/0/brando9/veribench/veribench_dataset/lean_src'
ENV = dict(os.environ, PATH='/lfs/skampere1/0/brando9/.elan/bin:' + os.environ['PATH'])

ALT = """You are writing a second, independent reference file for a Lean 4 formal-specification-coverage task. Below are the Python source and the existing reference file G (its proofs are `sorry`).

Write the file G' with these rules:
1. Keep `import Mathlib`, the namespace layout, the implementation definitions, the tests (`example`, `#eval`) and the pre-condition `Pre` exactly as in G.
2. For EVERY property definition (`*_prop`) and its theorem, restate the property in a logically equivalent but structurally different form: for example a contrapositive, a different quantifier layout, an explicit conjunction split in a different way, an iff instead of two implications, counts instead of permutation, a different helper definition. A pure renaming or reordering is not enough. Do not weaken it, do not strengthen it, do not drop any property, do not add properties. The two files must have the same obligations with the same weight.
3. Keep the same theorem names and the same number of theorems; each theorem proof is `by sorry`. Keep `Post_prop` and the correctness theorem consistent with your restated properties (their statements may be restated as well). Update docstrings to describe your form.
4. The file must compile with `lake env lean` in a Mathlib project, the only warnings being `declaration uses 'sorry'`.
Output only the complete Lean file inside one ```lean code block.

## Python source
```python
{py}
```

## G
```lean
{g}
```
"""
HALF = """Rewrite the Lean 4 file below, keeping the implementation, the tests, `Pre`, and ONLY the first half (rounded up) of its properties (each `*_prop` definition with its theorem), in file order. Delete every other property and theorem, and make `Post_prop` and the correctness theorem mention only the kept properties. Every theorem proof stays `by sorry`. The file must compile with `lake env lean` in a Mathlib project, the only warnings being `declaration uses 'sorry'`.
Output only the complete Lean file inside one ```lean code block.

```lean
{g}
```
"""
RETRY = "\n\nYour previous attempt was rejected: {why}\nFix this and output the complete Lean file again inside one ```lean code block.\n"


def lean_block(text):
    m = re.findall(r"```(?:lean4?|Lean)?\n(.*?)```", text, re.S)
    return max(m, key=len) if m else ''


def compile_lean(src, tag):
    d = HERE / 'materials' / '_compile'; d.mkdir(parents=True, exist_ok=True)
    f = d / f'{tag}.lean'; f.write_text(src)
    try:
        r = subprocess.run(['lake', 'env', 'lean', str(f)], cwd=LEAN_SRC, env=ENV, capture_output=True, text=True, timeout=600)
    except subprocess.TimeoutExpired:
        return False, 'compile timeout'
    out = r.stdout + r.stderr
    errs = [l for l in out.splitlines() if re.search(r'error', l)]
    return (r.returncode == 0 and not errs), ('\n'.join(errs[:6]) or out[-300:])


def gate(kind, g, new):
    th_g, th_n = theorem_names(g), theorem_names(new)
    if kind == 'half':
        if not th_n or not set(th_n) <= set(th_g) or len(th_n) >= len(th_g):
            return False, f'half file must keep a non-empty strict subset of the theorems: kept {th_n} of {th_g}'
        return True, 'ok'
    if th_g != th_n: return False, f'theorem names differ: {th_g} vs {th_n}'
    sim = similarity(g, new)
    if sim > 0.85: return False, f'too similar to G (statement similarity {sim:.2f} > 0.85); restate the properties more substantially'
    pg = [s for s in statements(g) if re.match(r'(?:@\[[^\]]*\]\s*)?(?:def|abbrev)\b', s)]
    pn = set(statements(new)); changed = sum(1 for s in pg if s not in pn)
    if pg and changed * 2 < len(pg): return False, f'only {changed} of {len(pg)} property definitions changed'
    return True, 'ok'


def job(task, kind, family):
    d = HERE / 'materials' / task; d.mkdir(parents=True, exist_ok=True)
    name = f'Gprime_{family}' if kind == 'alt' else 'H'
    out, meta = d / f'{name}.lean', d / f'{name}.gen.json'
    if out.exists(): return task, name, 'cached'
    g = (d / 'G.lean').read_text(); py = (HERE / 'inputs' / task / 'source.py').read_text()
    base = (ALT.format(py=py, g=g) if kind == 'alt' else HALF.format(g=g))
    prompt, tries = base, []
    for k in range(3):
        res = llm.ask(family if kind == 'alt' else 'codex', prompt, str(HERE / 'materials' / '_ws' / f'{task}_{name}_{k}'), f'{task}_{name}')
        new = lean_block(res.get('text', '')); rec = dict(attempt=k, plan=res.get('plan'), harness=res.get('harness'), model=res.get('model'), why=res.get('why'))
        if not new.strip(): rec['gate'] = 'no lean block'; tries.append(rec); prompt = base + RETRY.format(why='no Lean code block in the reply'); continue
        ok, why = gate(kind, g, new)
        if ok: ok, why = compile_lean(new, f'{task}_{name}_{k}')
        rec['gate'] = 'pass' if ok else why[:300]; tries.append(rec)
        if ok: out.write_text(new); break
        prompt = base + RETRY.format(why=why[:600])
    meta.write_text(json.dumps(dict(task=task, name=name, accepted=out.exists(), tries=tries), indent=1))
    return task, name, 'accepted' if out.exists() else 'FAILED'


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--kind', choices=['alt', 'half']); ap.add_argument('--family', choices=['codex', 'claude'], default='codex')
    ap.add_argument('--tasks'); ap.add_argument('--par', type=int, default=6); a = ap.parse_args()
    tasks = a.tasks.split(',') if a.tasks else json.load(open(HERE / 'inputs/tasks.json'))['tasks']
    with cf.ThreadPoolExecutor(a.par) as ex:
        for r in ex.map(lambda t: job(t, a.kind, a.family), tasks): print(*r, flush=True)
