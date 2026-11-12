from pathlib import Path
import subprocess,os,time,json
p=Path(__file__).resolve().parent
root=p.parents[2]
env=os.environ.copy()
for k in ('ANTHROPIC_API_KEY','ANTHROPIC_AUTH_TOKEN','ANTHROPIC_BASE_URL','OPENAI_API_KEY','GEMINI_API_KEY'):
 env.pop(k,None)
cmd=['claude','-p','--dangerously-skip-permissions','--model','claude-fable-5-1','--effort','max','--output-format','stream-json','--verbose', (p/'prompt.txt').read_text()]
(p/'launch.json').write_text(json.dumps({'model':'claude-fable-5-1','effort':'max','permission_mode':'bypassPermissions','route':'verified claude.ai Max subscription','started':time.time()},indent=2))
with (p/'stream.jsonl').open('w') as out,(p/'stderr.txt').open('w') as err:
 try:
  r=subprocess.run(cmd,cwd=root,env=env,stdout=out,stderr=err,timeout=1200)
  code=r.returncode
 except subprocess.TimeoutExpired:
  code=124
(p/'done.json').write_text(json.dumps({'exit':code,'ended':time.time()}))
