#!/usr/bin/env python3
"""Minimal frontier-model optimizing agent: GPT-6 Astra (reasoning high) with one tool, python(code), run in a scratch folder holding only train_only.json.
usage: agent_loop.py --name corr|ce --workdir DIR --prompt FILE --out DIR [--cap 15] [--turns 14]
Key read from a file named in the environment, never printed. Every request, tool call and result is appended to <out>/transcript.jsonl."""
import argparse, json, os, subprocess, sys, time, urllib.request, urllib.error
ap=argparse.ArgumentParser(); ap.add_argument('--name',required=True); ap.add_argument('--workdir',required=True); ap.add_argument('--prompt',required=True)
ap.add_argument('--out',required=True); ap.add_argument('--cap',type=float,default=15.0); ap.add_argument('--turns',type=int,default=14); a=ap.parse_args()
import os; KEY=open(os.environ['OPENAI_KEY_FILE']).read().strip()
os.makedirs(a.out,exist_ok=True); T=open(f'{a.out}/transcript.jsonl','a')
def log(**k): T.write(json.dumps(dict(t=time.strftime('%FT%T%z'),**k))+'\n'); T.flush()
tools=[{'type':'function','name':'python','description':'Run python3 code (numpy and scipy installed, no internet) in the working folder that holds train_only.json; stdout/stderr returned (truncated to 6000 chars). Files you write persist between calls.',
        'parameters':{'type':'object','properties':{'code':{'type':'string'}},'required':['code'],'additionalProperties':False}}]
inp=[{'role':'user','content':open(a.prompt).read()}]
cost=0.0
for turn in range(a.turns):
    body={'model':'gpt-6-astra','input':inp,'tools':tools,'reasoning':{'effort':'high'},'max_output_tokens':32000,'store':False,'include':['reasoning.encrypted_content']}
    req=urllib.request.Request('https://api.openai.com/v1/responses',data=json.dumps(body).encode(),headers={'Authorization':'Bearer '+KEY,'Content-Type':'application/json'})
    d=json.load(urllib.request.urlopen(req,timeout=1500)); u=d.get('usage',{})
    it=u.get('input_tokens',0); ct=(u.get('input_tokens_details') or {}).get('cached_tokens',0); ot=u.get('output_tokens',0)
    cost+=((it-ct)*10+ct*1+ot*50)/1e6; log(turn=turn,usage=u,cost_so_far=round(cost,4))
    inp+=d['output']; calls=[o for o in d['output'] if o['type']=='function_call']
    for o in d['output']:
        if o['type']=='message': log(assistant=''.join(x.get('text','') for x in o['content']))
    if not calls: break
    if cost>a.cap: log(stop='cost cap'); break
    for c in calls:
        code=json.loads(c['arguments'])['code']; log(tool_code=code)
        try:
            r=subprocess.run([sys.executable,'-I','-c',code],cwd=a.workdir,capture_output=True,text=True,timeout=300); out=(r.stdout+r.stderr)[-6000:]
        except subprocess.TimeoutExpired: out='TIMEOUT after 300 s'
        log(tool_result=out); inp.append({'type':'function_call_output','call_id':c['call_id'],'output':out or '(no output)'})
log(done=True,total_cost_usd=round(cost,4)); print('cost',round(cost,4))
