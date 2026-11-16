#!/usr/bin/env python3
"""Run frozen H2 judge prompts (75 artifacts) through OpenAI / Gemini APIs, 3 calls each, with a spend ledger and hard cap.
usage: run_judges.py --judge astra|sol61|argon [--limit N] [--repeats 3] [--cap USD]
Keys are read on this host from ~/keys (never printed)."""
import argparse, json, os, sys, time, threading, urllib.request, urllib.error, re
from concurrent.futures import ThreadPoolExecutor
KEYS=os.environ.get('KEYS_DIR','keys')
D=os.environ.get('WORK_DIR','work')
# $ per 1M tokens (standard tier; sources: vendor price pages as listed 2026-11-16)
J={'astra':dict(kind='openai',model='gpt-6-astra',key='openai_bm_key_koyejolab.txt',inp=10.0,cin=1.0,out=50.0,effort='high'),
   'sol61':dict(kind='openai',model='gpt-6.1-sol',key='openai_bm_key_koyejolab.txt',inp=2.0,cin=0.1,out=10.0,effort='high'),
   'argon':dict(kind='gemini',model='gemini-4-argon',key='gemini_allen_key.txt',inp=2.0,cin=0.1,out=10.0,effort='high')}
ap=argparse.ArgumentParser(); ap.add_argument('--judge',required=True); ap.add_argument('--limit',type=int,default=0)
ap.add_argument('--repeats',type=int,default=3); ap.add_argument('--cap',type=float,default=60.0); ap.add_argument('--conc',type=int,default=6)
ap.add_argument('--maxtok',type=int,default=32000)
a=ap.parse_args(); c=J[a.judge]
key=open(f'{KEYS}/{c["key"]}').read().strip()
rows=[json.loads(l) for l in open(f'{D}/prompts_h2_75.jsonl')]
if a.limit: rows=rows[:a.limit]
out=f'{D}/raw_{a.judge}'; os.makedirs(out,exist_ok=True)
lock=threading.Lock(); spent=[0.0]; stop=[False]
def parse(text):
    objs=[];depth=0;start=None;ins=False;esc=False
    for i,ch in enumerate(text):
        if ins:
            if esc: esc=False
            elif ch=='\\': esc=True
            elif ch=='"': ins=False
            continue
        if ch=='"': ins=True
        elif ch=='{':
            if depth==0: start=i
            depth+=1
        elif ch=='}' and depth:
            depth-=1
            if depth==0:
                try: objs.append(json.loads(text[start:i+1]))
                except Exception: pass
    vals={int(o['final_score_0_5']) for o in objs if isinstance(o,dict) and isinstance(o.get('final_score_0_5'),(int,float)) and not isinstance(o.get('final_score_0_5'),bool) and float(o['final_score_0_5']).is_integer() and 0<=o['final_score_0_5']<=5}
    if len(vals)!=1: raise ValueError('no/conflicting score')
    return vals.pop(), objs[0]
def post(url,body,hdr):
    req=urllib.request.Request(url,data=json.dumps(body).encode(),headers=hdr)
    with urllib.request.urlopen(req,timeout=1500) as r: return json.load(r)
def call(r):
    if c['kind']=='openai':
        d=post('https://api.openai.com/v1/responses',{'model':c['model'],'instructions':r['system'],'input':r['user'],'reasoning':{'effort':c['effort']},'max_output_tokens':a.maxtok,'store':False},
               {'Authorization':'Bearer '+key,'Content-Type':'application/json'})
        txt=''.join(x.get('text','') for o in d.get('output',[]) if o.get('type')=='message' for x in o.get('content',[]))
        u=d.get('usage',{}); it=u.get('input_tokens',0); ct=(u.get('input_tokens_details') or {}).get('cached_tokens',0); ot=u.get('output_tokens',0)
        rt=(u.get('output_tokens_details') or {}).get('reasoning_tokens',0); fin=d.get('status')+':'+str((d.get('incomplete_details') or {}).get('reason'))
    else:
        d=post(f'https://generativelanguage.googleapis.com/v1beta/models/{c["model"]}:generateContent',
               {'systemInstruction':{'parts':[{'text':r['system']}]},'contents':[{'role':'user','parts':[{'text':r['user']}]}],
                'generationConfig':{'maxOutputTokens':a.maxtok,'thinkingConfig':{'thinkingLevel':c['effort']}}},
               {'x-goog-api-key':key,'Content-Type':'application/json'})
        cand=(d.get('candidates') or [{}])[0]
        txt=''.join(p.get('text','') for p in (cand.get('content') or {}).get('parts',[]) if not p.get('thought'))
        u=d.get('usageMetadata',{}); it=u.get('promptTokenCount',0); ct=u.get('cachedContentTokenCount',0)
        rt=u.get('thoughtsTokenCount',0); ot=u.get('candidatesTokenCount',0)+rt; fin=str(cand.get('finishReason'))
    cost=((it-ct)*c['inp']+ct*c['cin']+ot*c['out'])/1e6
    return txt,dict(in_tokens=it,cached=ct,out_tokens=ot,reasoning_tokens=rt),cost,fin
def work(job):
    r,rep=job; f=f'{out}/{r["item"]}__r{rep}.json'
    if os.path.exists(f) and json.load(open(f)).get('status')=='COMPLETE': return
    worst=(len(r['system'])+len(r['user']))/3.0*c['inp']/1e6+a.maxtok*c['out']/1e6
    with lock:
        if stop[0] or spent[0]+worst>a.cap: stop[0]=True; return
        spent[0]+=worst; res=worst
    rec=dict(item=r['item'],task=r['task'],repeat=rep,judge=a.judge,model=c['model'],effort=c['effort'],started=time.strftime('%FT%T%z'))
    cost=0.0
    for attempt in (1,2,3):
        try:
            txt,use,cost,fin=call(r); rec.update(usage=use,cost_usd=round(cost,5),finish=fin,text=txt)
            try:
                s,o=parse(txt); rec.update(status='COMPLETE',score_raw=s,verdict=o)
            except ValueError as e: rec.update(status='PARSE_ERROR',error=str(e))
            break
        except urllib.error.HTTPError as e:
            body=e.read().decode()[:400]; rec.update(status='HTTP_%d'%e.code,error=body)
            if e.code in (429,500,502,503,529): time.sleep(20*attempt); continue
            break
        except Exception as e:
            rec.update(status='ERROR',error=repr(e)[:300]); time.sleep(10*attempt)
    with lock: spent[0]+=cost-res
    json.dump(rec,open(f,'w'),indent=1)
    print(r['item'],rep,rec['status'],rec.get('score_raw'),rec.get('usage'),rec.get('cost_usd'),flush=True)
jobs=[(r,k) for r in rows for k in range(1,a.repeats+1)]
with ThreadPoolExecutor(a.conc) as ex: list(ex.map(work,jobs))
print('SPENT_estimate_usd',round(spent[0],4),'stopped_on_cap',stop[0])
