"""Cross-family equivalence audit of each alternative reference G'x against G (experiment 24, admission gate 3).

Use: on skampere1 after gen_alt.py: python3 scripts/audit_equiv.py --gen codex  (G' written by gpt-6-astra, audited by claude-opus-5-5) and --gen claude (audited by gpt-6-astra). Needs python3, scripts/llm.py.
Writes materials/<task>/audit_<gen>.json = verdict per theorem plus 'all_equivalent'. Cached. Verdicts: equivalent, stronger, weaker, different (G' relative to G).
Example: python3 scripts/audit_equiv.py --gen codex --par 6
"""
import argparse, json, os, re, sys, pathlib, concurrent.futures as cf
sys.path.insert(0, os.path.dirname(__file__))
import llm
HERE = pathlib.Path(__file__).resolve().parents[1]
P = """You audit two Lean 4 formal-specification files for the same Python program: the reference G and a rewritten file G'. Proofs are `sorry` in both; judge the STATEMENTS only (the property definitions `*_prop`, their theorems, Pre, Post).

For each theorem name present in G, decide how G''s theorem relates to G's theorem, after unfolding the definitions each file uses:
- "equivalent": the two statements are logically equivalent for all inputs satisfying Pre (each implies the other);
- "stronger": G' implies G but not conversely;
- "weaker": G implies G' but not conversely;
- "different": neither implies the other, or G' is vacuous or about something else.
Be strict: say "equivalent" only when you can see why each direction holds. Also report whether the two files have the same implementation definitions and the same Pre ("same_impl": true or false).

## Python source
```python
{py}
```
## G
```lean
{g}
```
## G'
```lean
{gp}
```
Return only JSON: {{"theorems":[{{"name":"<theorem name>","verdict":"equivalent|stronger|weaker|different","reason":"<one sentence>"}}],"same_impl":true|false}}"""


def parse(t):
    m = re.search(r"\{.*\}", t, re.S)
    try: return json.loads(m.group(0))
    except Exception: return {}


def job(task, gen):
    d = HERE / 'materials' / task; src = d / f'Gprime_{gen}.lean'; out = d / f'audit_{gen}.json'
    if out.exists() or not src.exists(): return task, 'cached' if out.exists() else 'no G prime'
    aud = 'claude' if gen == 'codex' else 'codex'
    prompt = P.format(py=(HERE / 'inputs' / task / 'source.py').read_text(), g=(d / 'G.lean').read_text(), gp=src.read_text())
    res, js = {}, {}
    for k in range(2):
        res = llm.ask(aud, prompt, str(HERE / 'materials/_ws' / f'{task}_audit_{gen}_{k}'), f'{task}_audit')
        js = parse(res.get('text', ''))
        if js.get('theorems'): break
    th = js.get('theorems') or []
    rec = dict(task=task, gen_family=gen, auditor_family=aud, auditor_model=res.get('model'), harness=res.get('harness'), plan=res.get('plan'), theorems=th, same_impl=js.get('same_impl'),
               all_equivalent=bool(th) and all(t.get('verdict') == 'equivalent' for t in th) and js.get('same_impl') is not False, parsed=bool(th))
    out.write_text(json.dumps(rec, indent=1))
    return task, 'equivalent' if rec['all_equivalent'] else 'REJECTED'


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--gen', choices=['codex', 'claude'], required=True); ap.add_argument('--par', type=int, default=6); ap.add_argument('--tasks'); a = ap.parse_args()
    tasks = a.tasks.split(',') if a.tasks else json.load(open(HERE / 'inputs/tasks.json'))['tasks']
    with cf.ThreadPoolExecutor(a.par) as ex:
        for r in ex.map(lambda t: job(t, a.gen), tasks): print(*r, flush=True)
