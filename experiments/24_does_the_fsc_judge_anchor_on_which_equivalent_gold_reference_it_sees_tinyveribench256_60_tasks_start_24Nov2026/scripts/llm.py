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


def call(plan, prompt, ws, tag, note=NOTE):
    os.makedirs(ws, exist_ok=True)
    pf = os.path.abspath(os.path.join(ws, f'.prompt_{tag}_{uuid.uuid4().hex[:6]}.md'))
    open(pf, 'w').write(note + prompt)
    r = subprocess.run(ROUTER + ['run', '--plan', plan, '--prompt-file', pf, '--workspace', ws], capture_output=True, text=True)
    rec = None
    for l in reversed(r.stdout.strip().splitlines()):
        try: rec = json.loads(l); break
        except Exception: pass
    if not rec or 'logs' not in rec:
        return dict(ok=False, why='skipped: ' + (r.stderr.strip()[-200:] or 'no receipt'), plan=plan, text='')
    return dict(ok=(rec.get('status') == 'completed'), why=rec.get('status'), plan=plan, receipt={k: rec[k] for k in rec if k != 'logs'}, text=result_text(os.path.join(rec['logs'], 'stdout')), job=rec['logs'])


GATEWAY = 'https://aiapi-prod.stanford.edu/v1/chat/completions'
GATEWAY_MODELS = {'deepseek': 'DeepSeek V4.1 Flash 1017', 'kimi': 'Kimi K3'}
LEDGER = os.path.expanduser('~/.local/state/at3437-gateway.jsonl')
CAP_USD = 15.0  # experiment 24 cap on the Stanford gateway key (open-weight judges), reported cost from the gateway's own header
# which family's alternative reference G' each judge is shown (cross-family: no judge sees text it wrote)
GX_SRC = {'claude': 'codex', 'codex': 'claude', 'deepseek': 'codex', 'kimi': 'codex', 'agent_codex': 'claude', 'agent_deepseek': 'codex'}
OWN_SRC = {'claude': 'claude', 'codex': 'codex'}
LABEL = {'claude': ('Claude Code CLI, text only, single call', 'claude-opus-5-5'), 'codex': ('Codex CLI, text only, single call', 'gpt-6-astra'),
         'deepseek': ('Stanford gateway, single call', 'DeepSeek V4.1 Flash 1017 (open weights)'), 'kimi': ('Stanford gateway, single call', 'Kimi K3 (open weights)'),
         'agent_codex': ('Codex CLI agent (read, shell, Lean check)', 'gpt-6-astra'), 'agent_deepseek': ('Pi agent (read, shell, Lean check)', 'DeepSeek V4.1 Flash 1017 (open weights)')}


def spent():
    try: return sum(json.loads(l).get('cost', 0) for l in open(LEDGER))
    except OSError: return 0.0


def gateway(model_key, prompt, tag, tries=6):
    """One chat call to the Stanford gateway with the STAIR bm key (key read from the key file, never printed). Open-weight judges; temperature 0."""
    import urllib.request, urllib.error
    key = open(os.path.expanduser('~/keys/stanford_stair_bm_gateway_key.txt')).read().strip()
    os.makedirs(os.path.dirname(LEDGER), exist_ok=True)
    body = json.dumps(dict(model=GATEWAY_MODELS[model_key], messages=[dict(role='user', content=prompt)], temperature=0, max_tokens=8000)).encode()
    why = ''
    for k in range(tries):
        if spent() > CAP_USD: return dict(ok=False, why='skipped: experiment 24 gateway cap reached', plan='stanford-gateway', text='')
        req = urllib.request.Request(GATEWAY, body, {'Authorization': 'Bearer ' + key, 'Content-Type': 'application/json'})
        try:
            with urllib.request.urlopen(req, timeout=600) as r:
                d = json.loads(r.read()); cost = float(r.headers.get('x-litellm-response-cost') or 0)
            msg = d['choices'][0]['message']
            with open(LEDGER, 'a') as f: f.write(json.dumps(dict(tag=tag, model=GATEWAY_MODELS[model_key], cost=cost, usage=d.get('usage'), utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))) + '\n')
            return dict(ok=True, why='completed', plan='stanford-gateway', text=msg.get('content') or '', model=GATEWAY_MODELS[model_key], harness='Stanford gateway, single call', cost=cost)
        except urllib.error.HTTPError as e:
            why = f'HTTP {e.code}'; time.sleep(30 * (k + 1) if e.code in (429, 500, 502, 503, 504) else 5)
        except Exception as e:
            why = type(e).__name__; time.sleep(20)
    return dict(ok=False, why='gateway: ' + why, plan='stanford-gateway', text='')


def pi_agent(model_key, prompt, ws, tag):
    """One Pi agent run (read and bash tools only, no extensions, no MCP) with a Stanford-gateway open-weight model, working in ws."""
    os.makedirs(ws, exist_ok=True)
    if spent() > CAP_USD: return dict(ok=False, why='skipped: experiment 24 gateway cap reached', plan='stanford-gateway', text='')
    env = dict(os.environ, PATH='/dfs/scratch0/brando9/bin:' + os.path.expanduser('~/.local/bin') + ':' + os.environ['PATH'])
    cmd = [os.path.expanduser('~/.local/bin/pi'), '--provider', 'stanford-stair-bm', '--model', GATEWAY_MODELS[model_key], '--tools', 'read,bash', '--no-extensions', '--no-mcp', '--no-skills', '--no-prompt-templates',
           '--no-context-files', '--no-session', '--thinking', 'off', '--mode', 'json', '-p', prompt]
    try: r = subprocess.run(cmd, cwd=ws, capture_output=True, text=True, timeout=1200, env=env)
    except subprocess.TimeoutExpired: return dict(ok=False, why='timeout', plan='stanford-gateway', text='')
    msgs, usage = [], []
    for l in r.stdout.splitlines():
        try: d = json.loads(l)
        except ValueError: continue
        if d.get('type') == 'message_end' and d.get('message', {}).get('role') == 'assistant': msgs.append(d['message'])
    text = '\n'.join(c.get('text', '') for m in msgs[-1:] for c in m.get('content', []) if c.get('type') == 'text')
    with open(LEDGER, 'a') as f: f.write(json.dumps(dict(tag=tag, model=GATEWAY_MODELS[model_key], cost=0.01, note='pi agent run, flat estimate per run (Pi rates are 0)', turns=len(msgs), utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))) + '\n')
    return dict(ok=bool(text), why='completed' if text else 'no answer', plan='stanford-gateway', text=text, model=GATEWAY_MODELS[model_key], harness='Pi agent (read, shell, Lean check)', turns=len(msgs))


def ask(family, prompt, ws, tag, max_wait=14400, log=None):
    if family in GATEWAY_MODELS: return gateway(family, prompt, tag)
    if family == 'agent_deepseek': return pi_agent('deepseek', prompt, ws, tag)
    agent = family == 'agent_codex'
    lanes = LANES['codex' if agent else family]
    t0 = time.time(); skipped = []
    while True:
        for plan, harness, model in lanes:
            res = call(plan, prompt, ws, tag, note='' if agent else NOTE)
            res.update(harness=harness + (' agent' if agent else ''), model=model, family=family)
            if log: log(f'{tag} {plan} -> {res["why"]}')
            if res['why'] and str(res['why']).startswith('skipped'):
                skipped.append(res['why']); continue
            return res
        if time.time() - t0 > max_wait: return dict(ok=False, why='all lanes gated: ' + ' | '.join(skipped[-3:]), plan=None, text='', family=family)
        time.sleep(90)
