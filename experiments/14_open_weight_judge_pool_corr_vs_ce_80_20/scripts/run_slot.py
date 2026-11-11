"""Run open-weight judges on the exp-100 prompts (H0/H1/H2 x 75 artifacts) with a local vLLM server per model.
Usage: python run_slot.py --gpus 0,1 --models q25_7b,q3_8b --out DIR   (stdlib only; vllm from venv128)"""
import argparse, json, os, subprocess, sys, time, glob, urllib.request, concurrent.futures as cf
L='/lfs/mercury2/0/brando9'; PY=L+'/at979/venv128/bin'; HF='/dfs/scratch0/brando9/at1025_hf'
M={ # key: (hf dir name, tp, no_think)
 'q25_7b':('Qwen--Qwen2.5-7B-Instruct',2,0),'q25c_7b':('Qwen--Qwen2.5-Coder-7B-Instruct',2,0),
 'q3_8b':('Qwen--Qwen3-8B',2,1),'q3_4b_2507':('Qwen--Qwen3-4B-Instruct-2507',2,0),
 'llama31_8b':('unsloth--Llama-3.1-8B-Instruct',2,0),'mistral7b_v03':('mistralai--Mistral-7B-Instruct-v0.3',2,0),
 'granite33_8b':('ibm-granite--granite-3.3-8b-instruct',2,0),'hermes3_8b':('NousResearch--Hermes-3-Llama-3.1-8B',2,0),
 'glm4_9b':('zai-org--GLM-4-9B-0414',2,0),'olmo3_7b':('allenai--Olmo-3-7B-Instruct',2,0),
 'seed_coder_8b':('ByteDance-Seed--Seed-Coder-8B-Instruct',2,0),'phi4_mini':('microsoft--Phi-4-mini-instruct',2,0),
 'q3_30b_a3b_awq':('/dfs/scratch0/brando9/at1131_hf|cpatonn--Qwen3-30B-A3B-Instruct-2507-AWQ-4bit',2,0),
 'q25c_14b':('Qwen--Qwen2.5-Coder-14B-Instruct',4,0),'q3_14b':('Qwen--Qwen3-14B',4,1),
}
ap=argparse.ArgumentParser(); ap.add_argument('--gpus',required=True); ap.add_argument('--models',required=True)
ap.add_argument('--out',required=True); ap.add_argument('--prompts',default='/dfs/scratch0/brando9/at2937/prompts.jsonl')
ap.add_argument('--port',type=int,default=18700); ap.add_argument('--conc',type=int,default=4); ap.add_argument('--n',type=int,default=4)
a=ap.parse_args(); os.makedirs(a.out,exist_ok=True)
P=[json.loads(l) for l in open(a.prompts)]
def snap(d):
    root=HF
    if '|' in d: root,d=d.split('|')
    return sorted(glob.glob(f'{root}/hub/models--{d}/snapshots/*'))[0]
def call(port,name,r,nothink):
    body={'model':name,'messages':[{'role':'system','content':r['system']},{'role':'user','content':r['user']}],
          'temperature':0.7,'top_p':0.95,'max_tokens':700,'n':a.n}
    if nothink: body['chat_template_kwargs']={'enable_thinking':False}
    for att in range(2):
        try:
            rq=urllib.request.Request(f'http://127.0.0.1:{port}/v1/chat/completions',json.dumps(body).encode(),{'Content-Type':'application/json'})
            d=json.load(urllib.request.urlopen(rq,timeout=1500))
            return {'item':r['item'],'prompt':r['prompt'],'texts':[c['message']['content'] for c in d['choices']],'usage':d.get('usage')}
        except urllib.error.HTTPError as e:
            return {'item':r['item'],'prompt':r['prompt'],'error':f'HTTP {e.code} '+e.read().decode()[:300]}
        except Exception as e: err=repr(e)
    return {'item':r['item'],'prompt':r['prompt'],'error':err}
for key in a.models.split(','):
    hfd,tp,nothink=M[key]; fin=f'{a.out}/{key}.jsonl'
    if os.path.exists(fin+'.done'): continue
    gp=a.gpus.split(','); gp=','.join(gp[:tp]); t0=time.time()
    env=dict(os.environ,CUDA_VISIBLE_DEVICES=gp,HF_HUB_OFFLINE='1',VLLM_USE_FLASHINFER_SAMPLER='0',HF_HOME=HF,PATH=PY+':'+os.environ['PATH'])
    log=open(f'{a.out}/{key}.serve.log','w')
    sp=subprocess.Popen([PY+'/vllm','serve',snap(hfd),'--served-model-name',key,'--host','127.0.0.1','--port',str(a.port),'--max-model-len','24576',
        '--tensor-parallel-size',str(tp),'--gpu-memory-utilization','0.90','--max-num-seqs','6','--dtype','bfloat16'],env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
    up=False
    for i in range(120):
        if sp.poll() is not None: break
        try: urllib.request.urlopen(f'http://127.0.0.1:{a.port}/v1/models',timeout=3); up=True; break
        except Exception: time.sleep(10)
    if not up:
        print(key,'FAILED to start',flush=True); open(fin+'.failed','w').write('start failed'); 
        try: os.killpg(sp.pid,9)
        except Exception: pass
        continue
    print(key,'up after',int(time.time()-t0),'s',flush=True)
    order=sorted(P,key=lambda r:(r['prompt'],r['item']))
    with cf.ThreadPoolExecutor(a.conc) as ex, open(fin,'w') as f:
        for res in ex.map(lambda r:call(a.port,key,r,nothink),order):
            res['model']=key; f.write(json.dumps(res)+'\n'); f.flush()
    open(fin+'.done','w').write(str(time.time()-t0)); print(key,'done',int(time.time()-t0),'s',flush=True)
    try: os.killpg(sp.pid,15)
    except Exception: pass
    time.sleep(15)
