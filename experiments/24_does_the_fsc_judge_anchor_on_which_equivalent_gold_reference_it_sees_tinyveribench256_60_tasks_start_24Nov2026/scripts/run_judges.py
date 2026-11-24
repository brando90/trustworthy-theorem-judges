"""Run the judge cells of experiment 24: 15 cells per task for one judge family (rubric of experiment 09, exp 23 blind-judge prompt, only the Lean files vary).

Use: on skampere1 after gen_alt.py and audit_equiv.py: python3 scripts/run_judges.py --judge claude|codex|deepseek|kimi|agent_codex|agent_deepseek [--par 8] [--limit N] [--arms B,A] [--first-tasks N]. Needs python3 and scripts/llm.py (plan router, Stanford and Vals lanes first; Stanford gateway for open weights).
Judges (see llm.LABEL): claude-opus-5-5 and gpt-6-astra single calls (text only), DeepSeek V4.1 Flash and Kimi K3 single calls (open weights, gateway), gpt-6-astra as a Codex agent and DeepSeek V4.1 Flash as a Pi agent (read, shell, Lean check in a workspace). Each judge is shown the G' of the other family (llm.GX_SRC). Writes results/<judge>/raw/<task>__<cand>__<ref>.txt (cached, never re-asked), results/<judge>/receipts.jsonl and results/<judge>/cells.csv.
Example: python3 scripts/run_judges.py --judge claude --par 8
"""
import argparse, csv, hashlib, json, os, random, re, sys, threading, time, pathlib, concurrent.futures as cf
sys.path.insert(0, os.path.dirname(__file__))
import llm
from llm import GX_SRC, OWN_SRC
HERE = pathlib.Path(__file__).resolve().parents[1]
RUBRIC = (HERE / 'inputs/rubric_exp09.md').read_text().split('## Output format')[0]
TAIL = ('\nReturn only JSON: {"A":"Y|N","B":"Y|N","C":"Y|N","D":"none|handful|dominates","final_score_0_5":<integer 0-5>,'
        '"rationale":"<one sentence>"}')
NOGOLD = "(No gold Lean file is provided for this problem. Judge coverage of the specifications that the Python source implies.)"
_lock = threading.Lock()
ARMS = {'B': [(c, r) for c in ('G', 'Gx') for r in ('G', 'Gx', 'none')],
        'A': [('N', r) for r in ('G', 'Gx', 'Gown', 'none')],
        'C': [('H', r) for r in ('G', 'Gx', 'none')],
        'D': [('N', 'H'), ('N', 'Gother')]}


def parse(t):
    m = re.search(r"\{.*\}", t, re.S)
    try: return json.loads(m.group(0))
    except Exception: return {}


def audit_ok(task, gen):
    p = HERE / 'materials' / task / f'audit_{gen}.json'
    return p.exists() and json.load(open(p)).get('all_equivalent') is True


def files_for(task, judge):
    """Return {name: path} of the files this judge may use for the task, honouring the gates."""
    d = HERE / 'materials' / task; other, own = GX_SRC[judge], OWN_SRC.get(judge)
    f = {'G': d / 'G.lean', 'N': d / 'N.lean', 'Gother': d / 'Gother.lean'}
    if (d / f'Gprime_{other}.lean').exists() and audit_ok(task, other): f['Gx'] = d / f'Gprime_{other}.lean'
    if own and (d / f'Gprime_{own}.lean').exists() and audit_ok(task, own): f['Gown'] = d / f'Gprime_{own}.lean'
    if (d / 'H.lean').exists(): f['H'] = d / 'H.lean'
    return f


def cells_for(task, judge):
    f = files_for(task, judge); out = []
    for arm, cs in ARMS.items():
        for c, r in cs:
            if c != 'N' and c not in f and c != 'G': continue
            if c in f and (r == 'none' or r in f): out.append((arm, c, r))
    if 'Gx' not in f: out = []  # primary arms need G'x; the task is dropped for this judge
    return out, f


AGENT_HEAD = """You are working in a directory with these files: source.py (the Python program), candidate.lean (the agent Lean file you grade){gold_note}. Read them with your tools. You may also compile a Lean file with `./check.sh <file>` (it prints Lean's errors and warnings); use it only if it helps you judge. Do not modify the files. Then grade as the rubric below says and finish with the JSON reply it asks for.

"""
CHECK_SH = "#!/bin/bash\ncd /lfs/skampere1/0/brando9/vb90_grading/lean_project && PATH=/lfs/skampere1/0/brando9/.elan/bin:$PATH timeout 300 lake env lean \"$OLDPWD/$1\" 2>&1 | head -60\n"


def build_prompt(task, c, r, f, agent, ws):
    py = (HERE / 'inputs' / task / 'source.py').read_text()
    if not agent:
        gold = NOGOLD if r == 'none' else "```lean\n" + f[r].read_text() + "\n```"
        return (RUBRIC + "\n## Python source\n```python\n" + py + "\n```\n## Gold Lean file\n" + gold + "\n## Agent Lean file (candidate.lean)\n```lean\n" + f[c].read_text() + "\n```\n" + TAIL)
    os.makedirs(ws, exist_ok=True)
    (ws / 'source.py').write_text(py); (ws / 'candidate.lean').write_text(f[c].read_text())
    if r != 'none': (ws / 'gold.lean').write_text(f[r].read_text())
    (ws / 'check.sh').write_text(CHECK_SH); os.chmod(ws / 'check.sh', 0o755)
    note = ", gold.lean (the gold Lean file)" if r != 'none' else ""
    gold = "(gold.lean is in the directory.)" if r != 'none' else NOGOLD
    return (AGENT_HEAD.format(gold_note=note) + RUBRIC + "\n## Python source\n(in source.py)\n## Gold Lean file\n" + gold + "\n## Agent Lean file (candidate.lean)\n(in candidate.lean)\n" + TAIL)


def job(judge, task, arm, c, r, f, root):
    raw = root / 'raw' / f'{task}__{c}__{r}.txt'
    if not raw.exists():
        agent = judge.startswith('agent_')
        reply, attempt = '', 0
        while attempt < 2 and 'final_score_0_5' not in parse(reply):
            attempt += 1; t0 = time.time()
            ws = pathlib.Path(os.environ.get('EXP24_WS', str(HERE / 'materials/_ws'))) / f'{judge}_{task}_{c}_{r}_{attempt}'
            p = build_prompt(task, c, r, f, agent, ws)
            res = llm.ask(judge, p, str(ws), f'{task}_{c}_{r}')
            reply = res.get('text', '')
            with _lock, open(root / 'receipts.jsonl', 'a') as fh:
                fh.write(json.dumps(dict(task=task, arm=arm, cand=c, ref=r, judge=judge, model=res.get('model'), harness=res.get('harness'), plan=res.get('plan'), status=res.get('why'), cost=res.get('cost'), turns=res.get('turns'),
                                         attempt=attempt, prompt_sha256=hashlib.sha256(p.encode()).hexdigest(), reply_sha256=hashlib.sha256(reply.encode()).hexdigest(), parsed='final_score_0_5' in parse(reply),
                                         seconds=round(time.time() - t0, 1), utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))) + '\n')
        raw.write_text(reply)
    d = parse(raw.read_text())
    return dict(task=task, arm=arm, cand=c, ref=r, score=d.get('final_score_0_5', ''), A=d.get('A', ''), B=d.get('B', ''), C=d.get('C', ''), D=d.get('D', ''), rationale=d.get('rationale', ''))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--judge', choices=list(GX_SRC), required=True); ap.add_argument('--arms', default='B,A,C,D'); ap.add_argument('--first-tasks', type=int, default=0); ap.add_argument('--par', type=int, default=8); ap.add_argument('--limit', type=int, default=0); a = ap.parse_args()
    root = HERE / 'results' / a.judge; (root / 'raw').mkdir(parents=True, exist_ok=True)
    tasks = json.load(open(HERE / 'inputs/tasks.json'))['tasks']; jobs, dropped, used = [], [], 0
    for t in tasks:
        cells, f = cells_for(t, a.judge)
        cells = [x for x in cells if x[0] in a.arms.split(',')]
        if not cells: dropped.append(t); continue
        if a.first_tasks and used >= a.first_tasks: continue
        used += 1; jobs += [(a.judge, t, arm, c, r, f, root) for arm, c, r in cells]
    random.Random(24).shuffle(jobs)
    if a.limit: jobs = jobs[:a.limit]
    json.dump(dict(judge=a.judge, dropped_tasks=dropped, n_jobs=len(jobs)), open(root / 'plan.json', 'w'), indent=1)
    print('jobs', len(jobs), 'dropped tasks', len(dropped), flush=True)
    with cf.ThreadPoolExecutor(a.par) as ex: rows = list(ex.map(lambda j: job(*j), jobs))
    with open(root / 'cells.csv', 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0]), lineterminator='\n'); w.writeheader(); w.writerows(rows)
    print('done', len(rows), 'missing', sum(1 for r in rows if r['score'] == ''))
