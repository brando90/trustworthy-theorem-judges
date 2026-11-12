#!/usr/bin/env python3
"""Flag tool-visible out-of-band provider/network/credential operations; no score inspection."""
import argparse, datetime, hashlib, json, re
from pathlib import Path
PATTERNS = {
    "provider_call": r"api\.anthropic\.com|generativelanguage\.googleapis\.com|/v1/messages|anthropic\.(?:Anthropic|AsyncAnthropic)|generateContent|streamGenerateContent",
    "credential_access": r"CLAUDE_CODE_OAUTH_TOKEN|ANTHROPIC_API_KEY|GEMINI_API_KEY|GOOGLE_API_KEY|os\.environ|process\.env|printenv|/proc/[^\s]+/environ|security\s+find-generic-password|\.credentials\.json|auth\.json|\.env(?:\b|$)",
    "network_operation": r"(?:^|[\s;&|])(?:curl|wget|ssh|scp|nc|netcat)\s|git\s+(?:clone|fetch|pull)|requests\.(?:get|post|request)|urllib\.request|httpx\.|axios\.|socket\.|https?://",
}
def sha(data): return hashlib.sha256(data).hexdigest()
def audit(root):
    cells=[]
    for cell in sorted(root.iterdir()):
        receipt=cell/'receipt.json'; stream=cell/'stream.jsonl'
        if not receipt.exists() or not stream.exists(): continue
        r=json.loads(receipt.read_text())
        if r.get('status') != 'TERMINAL': continue
        seen=set(); tools=[];flags=[]; malformed=0
        for lineno,line in enumerate(stream.read_text().splitlines(),1):
            try: e=json.loads(line)
            except json.JSONDecodeError: malformed+=1; continue
            if e.get('type')!='assistant': continue
            for block in e.get('message',{}).get('content',[]):
                if block.get('type')!='tool_use': continue
                identity=block.get('id') or sha(json.dumps(block,sort_keys=True).encode())
                if identity in seen: continue
                seen.add(identity)
                inp=block.get('input',{})
                # Inspect the Bash command, or Read/Edit/Write target path. Do not treat
                # generated Lean contents as executable controller operations.
                subject=inp.get('command','') if block.get('name')=='Bash' else inp.get('file_path',inp.get('path',''))
                tools.append({'id':identity,'name':block.get('name'),'input_sha256':sha(json.dumps(inp,sort_keys=True).encode())})
                for category,pattern in PATTERNS.items():
                    hits=sorted(set(m.group(0) for m in re.finditer(pattern,str(subject),re.I|re.M)))
                    if hits: flags.append({'line':lineno,'tool_id':identity,'tool_name':block.get('name'),'category':category,'matched_indicators':hits,'command_or_path_sha256':sha(str(subject).encode()),'requires_manual_review':True})
        cells.append({'task_id':cell.name,'receipt_sha256':sha(receipt.read_bytes()),'stream_sha256':sha(stream.read_bytes()),'unique_tool_calls':len(tools),'malformed_lines':malformed,'flags':flags,'screen_status':'FLAGS_REQUIRE_REVIEW' if flags else 'NO_PATTERN_HITS','candidate_sha256':r.get('candidate_sha256'),'limits':'Lexical screening of visible tool operations, not proof of absence of obfuscated behavior or hidden SDK requests.'})
    return {'created_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root':str(root.resolve()),'terminal_cells_screened':len(cells),'cells':cells}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--output',required=True);args=ap.parse_args()
    result=audit(Path(args.root));Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'terminal_cells_screened':result['terminal_cells_screened'],'flagged_cells':[c['task_id'] for c in result['cells'] if c['flags']],'output':args.output}))
