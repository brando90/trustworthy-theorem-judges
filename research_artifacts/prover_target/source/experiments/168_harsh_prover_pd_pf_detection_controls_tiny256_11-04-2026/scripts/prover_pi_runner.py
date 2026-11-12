#!/usr/bin/env python3
# TLDR: Serial, capped, staged runner that asks Pi (tools disabled, Koyejo-lab OpenAI route, reasoning high) to prove each labeled case's immutable goal, checks every proof with the cases checker, and writes hash-bound receipts with measured cost per call.
"""Usage on skampere2 (key never passes through this script; Pi reads its own provider config):
  python3 prover_pi_runner.py --manifest cases/manifest.json --checker scripts/cases_check.py \
      --model gpt-6-astra --rung astra_high_fb4 --max-rounds 4 --cap-usd 30 --limit 12 --out results/prover_astra_high_fb4
Stop file: create <out>/STOP to stop before the next call. No retries, no model or key substitution.
"""
import argparse, hashlib, importlib.util, json, os, re, subprocess, sys, time
from pathlib import Path

PROVIDER = 'koyejolab-openai-bm'          # Koyejo-lab OpenAI key via Pi; never the personal or Vals providers
IN_PER_M, OUT_PER_M = 10.0, 50.0           # USD per million tokens, observed from gpt-6-astra preflight; reservation only
MAX_OUT_TOKENS = 16384                     # reservation assumption per call (Pi has no cap flag); real cost is read from Pi
PROMPT = ('You are a Lean 4.22.0 prover with Mathlib. Prove ONLY the immutable forward implication goal below. '
          'The definitions are supplied, with all implementation functions universally quantified. You may use the '
          'hypotheses and ordinary Mathlib lemmas. No reference proof or implementation is available. A stronger '
          'hypothesis is allowed; reverse implication is NOT required. Attempt a real proof. Return ONLY one Lean proof '
          'term (normally `by ...`), without markdown, theorem declarations, imports, commands, added hypotheses, '
          'sorry/admit, native_decide, axioms, unsafe code or metaprogramming. If no proof is found, return NOT_PROVED; '
          'do not assert non-entailment merely because search failed. The target cannot be changed.\n\n')
SECRET = re.compile(r'(sk-[A-Za-z0-9_-]{8,}|Bearer\s+[A-Za-z0-9._-]{12,})')

def sha(b): return hashlib.sha256(b if isinstance(b, bytes) else b.encode()).hexdigest()
def redact(s): return SECRET.sub('[REDACTED]', s)
def save(p, d):
    p = Path(p); p.parent.mkdir(parents=True, exist_ok=True)
    t = p.with_suffix(p.suffix + '.tmp'); t.write_text(json.dumps(d, indent=2) + '\n'); t.replace(p)

def load_checker(path):
    spec = importlib.util.spec_from_file_location('cases_check', path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m.check_case

def call_pi(model, thinking, prompt, timeout=900):
    cmd = ['pi', '-p', '--no-session', '--no-tools', '--no-extensions', '--no-mcp', '--no-skills', '--no-context-files',
           '--no-prompt-templates', '--no-themes', '--provider', PROVIDER, '--model', model, '--thinking', thinking,
           '--mode', 'json', '--', prompt]
    t = time.monotonic()
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env={'PATH': os.environ['PATH'], 'HOME': os.environ['HOME']})
    out = {'exit': p.returncode, 'seconds': time.monotonic() - t, 'stdout': redact(p.stdout), 'stderr': redact(p.stderr[-2000:])}
    msg = None
    for ln in p.stdout.splitlines():
        try: d = json.loads(ln)
        except Exception: continue
        m = d.get('message') or {}
        if d.get('type') == 'message_end' and m.get('role') == 'assistant': msg = m
    out['message'] = msg
    return out

def extract(msg):
    text = ''.join(c.get('text', '') for c in (msg.get('content') or []) if c.get('type') == 'text').strip()
    m = re.fullmatch(r'```(?:lean4?|Lean)?\s*\n(.*?)\n```', text, re.S)
    return m.group(1) if m else text

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--manifest', required=True); ap.add_argument('--checker', required=True)
    ap.add_argument('--model', required=True); ap.add_argument('--thinking', default='high')
    ap.add_argument('--rung', required=True); ap.add_argument('--max-rounds', type=int, default=4)
    ap.add_argument('--cap-usd', type=float, required=True); ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--start', type=int, default=0); ap.add_argument('--out', required=True)
    ap.add_argument('--ids', help='optional file with one case_id per line (fixed batch order)')
    a = ap.parse_args()
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    if (out / 'ledger.json').exists() and not os.environ.get('E168_RESUME'):
        sys.exit('ledger exists: no implicit replay; set E168_RESUME=1 only to continue an interrupted batch (completed cases are skipped)')
    check_case = load_checker(a.checker)
    man = json.loads(Path(a.manifest).read_text()); rows = man['rows'] if isinstance(man, dict) else man
    rows = [r for r in rows if r.get('eligible')]
    if a.ids: order = Path(a.ids).read_text().split(); rows = [next(r for r in rows if r['case_id'] == i) for i in order]
    rows = rows[a.start:a.start + a.limit] if a.limit else rows[a.start:]
    ledger = json.loads((out / 'ledger.json').read_text()) if (out / 'ledger.json').exists() else {'rung': a.rung, 'model': a.model, 'provider': PROVIDER, 'thinking': a.thinking, 'cap_usd': a.cap_usd, 'prompt_sha256': sha(PROMPT), 'spent_usd': 0.0, 'calls': []}
    results, consecutive_fail = [], 0
    for row in rows:
        cid = row['case_id']; rpath = out / f'{cid}.json'
        if rpath.exists(): results.append(json.loads(rpath.read_text())); continue
        goal = Path(row['goal_file']).read_text()
        history, attempts, status = '', [], 'not_proved'
        for rnd in range(a.max_rounds + 1):
            if (out / 'STOP').exists(): save(out / 'stop.json', {'reason': 'STOP file'}); return finish(out, ledger, results)
            reserve = (len(PROMPT + goal + history) / 3 * IN_PER_M + MAX_OUT_TOKENS * OUT_PER_M) / 1e6
            if ledger['spent_usd'] + reserve > a.cap_usd:
                save(out / 'stop.json', {'reason': 'cap', 'spent_usd': ledger['spent_usd'], 'next_reserve_usd': reserve}); return finish(out, ledger, results)
            prompt = PROMPT + goal + history
            call = {'case_id': cid, 'round': rnd, 'prompt_sha256': sha(prompt), 'reserved_usd': reserve, 'status': 'inflight'}
            ledger['calls'].append(call); save(out / 'ledger.json', ledger)
            try: r = call_pi(a.model, a.thinking, prompt)
            except subprocess.TimeoutExpired: r = {'exit': 124, 'message': None, 'stdout': '', 'stderr': 'timeout', 'seconds': 900}
            msg = r['message']; ok = bool(msg) and msg.get('stopReason') == 'stop' and not msg.get('errorMessage') and msg.get('model') == a.model and msg.get('provider') == PROVIDER
            cost = ((msg or {}).get('usage') or {}).get('cost', {}).get('total', 0.0) or 0.0
            call.update(status='completed' if ok else 'failed', cost_usd=cost, usage=(msg or {}).get('usage'), stop_reason=(msg or {}).get('stopReason'),
                        error=redact(str((msg or {}).get('errorMessage') or r['stderr'])[:300]), response_sha256=sha(r['stdout']), seconds=r['seconds'])
            ledger['spent_usd'] += cost; save(out / 'ledger.json', ledger)
            (out / 'raw').mkdir(exist_ok=True); (out / 'raw' / f'{cid}_r{rnd}.json').write_text(r['stdout'])
            if not ok:
                consecutive_fail += 1; status = 'model_call_failed'
                if consecutive_fail >= 2: save(out / 'stop.json', {'reason': 'two consecutive failed calls', 'last': call}); return finish(out, ledger, results)
                break
            consecutive_fail = 0
            proof = extract(msg)
            if proof == 'NOT_PROVED': status = 'declined'; attempts.append({'round': rnd, 'declined': True}); break
            chk = check_case(cid, proof, str(out / 'check' / f'{cid}_r{rnd}'))
            attempts.append({'round': rnd, 'proof_sha256': sha(proof), 'check': {k: chk.get(k) for k in ('accepted', 'status', 'axioms', 'seconds')}})
            if chk.get('accepted'): status = 'proved'; break
            log = ''
            lp = chk.get('compiler_log_path')
            if lp and Path(lp).exists(): log = Path(lp).read_text()[-14000:]
            history += '\nPrevious proof:\n' + proof + '\nLean feedback:\n' + (log or str(chk.get('status'))) + '\nRepair only the proof term. The goal and definitions are immutable.\n'
        res = {'case_id': cid, 'family': row.get('family'), 'label': row.get('label'), 'task': row.get('task'), 'status': status, 'credited': status == 'proved', 'attempts': attempts}
        save(rpath, res); results.append(res)
        print(cid, status, f"spent=${ledger['spent_usd']:.4f}", flush=True)
        if row.get('label') == 'H0' and status == 'proved':
            save(out / 'stop.json', {'reason': 'FALSE ALARM: a labeled-bad case was credited; inspect before continuing', 'case_id': cid}); return finish(out, ledger, results)
    finish(out, ledger, results)

def finish(out, ledger, results):
    save(out / 'summary.json', {'spent_usd': ledger['spent_usd'], 'cap_usd': ledger['cap_usd'], 'cases_done': len(results),
         'credited': sum(r['credited'] for r in results), 'by_status': {s: sum(r['status'] == s for r in results) for s in {r['status'] for r in results}}})
    print('done', json.dumps(json.loads((out / 'summary.json').read_text())))

if __name__ == '__main__':
    main()
