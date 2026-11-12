from pathlib import Path
import subprocess,os,time,json
p=Path(__file__).resolve().parent
root=p.parents[2]
env=os.environ.copy()
for k in list(env):
 if k.startswith('ANTHROPIC_') or k in ('OPENAI_API_KEY','GEMINI_API_KEY','CLAUDE_CODE_USE_BEDROCK','CLAUDE_CODE_USE_VERTEX','CLAUDE_CODE_USE_FOUNDRY'):env.pop(k,None)
cmd=['claude','-p','--dangerously-skip-permissions','--model','claude-fable-5-1','--effort','max','--output-format','stream-json','--verbose',(p/'prompt.txt').read_text()]
(p/'launch.json').write_text(json.dumps({'model':'claude-fable-5-1','effort':'max','permissions':'bypassPermissions','route':'verified claude.ai Max subscription','started_epoch':time.time(),'wrapper_pid':os.getpid()},indent=2)+'\n')
with (p/'stream.jsonl').open('w') as out,(p/'stderr.txt').open('w') as err:
 child=subprocess.Popen(cmd,cwd=root,env=env,stdout=out,stderr=err)
 (p/'worker.json').write_text(json.dumps({'pid':child.pid,'model':'claude-fable-5-1','effort':'max'})+'\n')
 code=child.wait()
(p/'done.json').write_text(json.dumps({'exit_code':code,'ended_epoch':time.time()})+'\n')
