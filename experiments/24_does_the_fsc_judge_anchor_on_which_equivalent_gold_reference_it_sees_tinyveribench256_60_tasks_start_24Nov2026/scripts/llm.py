"""One text-only model call through Brando's plan router on skampere1, by model family, Stanford and Vals lanes first (experiment 24).

Use: imported by gen_alt.py, audit_equiv.py and run_judges.py on skampere1. Needs python3 and ~/.config/plan-router/frap.json (router config copy).
Families: 'claude' = claude-opus-5-5 (lanes stanford-claude, vals-claude-opus, then personal-claude), 'codex' = gpt-6-astra (stanford-codex, then personal-codex). No agy, no API key, no paid fallback.
Example: from llm import ask; r = ask('claude', 'Say OK', '/tmp/ws1', 'probe'); print(r['text'], r['plan'], r['model'])
"""
import json, os, subprocess, sys, time, uuid
ROUTER = [sys.executable, os.path.expanduser('~/.local/lib/plan-router/router.py'), '--config', os.path.expanduser('~/.config/plan-router/frap.json')]
LANES = {'claude': [('stanford-claude', 'Claude Code (Stanford)', 'claude-opus-5-5'), ('vals-claude-opus', 'Claude Code (Vals)', 'claude-opus-5-5'),
                    ('personal-claude', 'Claude Code (personal)', 'claude-opus-5-5')],
         'codex': [('stanford-codex', 'Codex CLI (Stanford)', 'gpt-6-astra high'), ('personal-codex', 'Codex CLI (personal)', 'gpt-6-astra high')]}
FAMILY_MODEL = {'claude': 'claude-opus-5-5', 'codex': 'gpt-6-astra'}
NOTE = ("Answer from the text below only. Do not use tools, do not read or write files, do not run commands.\n\n")


def result_text(stdout_path):
    txt = []
    try: raw = open(stdout_path, errors='ignore').read()
    except OSError: return ''
    try:
        d = json.loads(raw)
        if isinstance(d, dict) and 'result' in d: return str(d['result'])
        if isinstance(d, list):
            for e in d:
                if e.get('type') == 'result': return str(e.get('result', ''))
    except Exception: pass
    for l in raw.splitlines():
        try: e = json.loads(l)
        except Exception: continue
        t = e.get('type')
        if t == 'item.completed':
            it = e.get('item', {})
            if it.get('type') == 'agent_message': txt.append(it.get('text', ''))
        elif t == 'result': txt.append(str(e.get('result', '')))
    return '\n'.join(txt)


def call(plan, prompt, ws, tag):
    os.makedirs(ws, exist_ok=True)
    pf = os.path.abspath(os.path.join(ws, f'.prompt_{tag}_{uuid.uuid4().hex[:6]}.md'))
    open(pf, 'w').write(NOTE + prompt)
    r = subprocess.run(ROUTER + ['run', '--plan', plan, '--prompt-file', pf, '--workspace', ws], capture_output=True, text=True)
    rec = None
    for l in reversed(r.stdout.strip().splitlines()):
        try: rec = json.loads(l); break
        except Exception: pass
    if not rec or 'logs' not in rec:
        return dict(ok=False, why='skipped: ' + (r.stderr.strip()[-200:] or 'no receipt'), plan=plan, text='')
    return dict(ok=(rec.get('status') == 'completed'), why=rec.get('status'), plan=plan, receipt={k: rec[k] for k in rec if k != 'logs'}, text=result_text(os.path.join(rec['logs'], 'stdout')), job=rec['logs'])


def ask(family, prompt, ws, tag, max_wait=14400, log=None):
    """Try the family's lanes in order; when all are gated wait 90 s and try again, up to max_wait seconds."""
    t0 = time.time(); skipped = []
    while True:
        for plan, harness, model in LANES[family]:
            res = call(plan, prompt, ws, tag)
            res.update(harness=harness, model=model, family=family)
            if log: log(f'{tag} {plan} -> {res["why"]}')
            if res['why'] and str(res['why']).startswith('skipped'):
                skipped.append(res['why']); continue
            return res
        if time.time() - t0 > max_wait: return dict(ok=False, why='all lanes gated: ' + ' | '.join(skipped[-3:]), plan=None, text='', family=family)
        time.sleep(90)
