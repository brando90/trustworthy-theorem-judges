#!/usr/bin/env python3
"""TLDR: Bind statement-only inputs to fixed goals and independently replay every credited proof."""
import hashlib
import json
import os
import re
import secrets
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PRIVATE = ROOT.parents[3] / 'private/fresh_prover_target/v2'
DEPENDENCIES = PRIVATE / 'dependencies'
LEAN_PROJECT = Path.home() / 'veribench/veribench_dataset/lean_src'
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
SPEC_ONLY = '''import Mathlib
import Lean
open Lean Elab Command
elab "specification " n:ident " : " ty:term " := " body:str : command => do
  let env ← getEnv
  match Parser.runParserCategory env `term body.getString with
  | .error msg => throwError "Specification must be exactly one Lean term: {msg}"
  | .ok term =>
    let parsed : TSyntax `term := ⟨term⟩
    let cmd ← `(def $n : $ty := $parsed)
    elabCommand cmd
'''
FORBIDDEN = {'sorry', 'admit', 'sorryAx', 'native_decide', 'axiom', 'run_tac', 'set_option',
             'macro', 'macro_rules', 'elab', 'elab_rules', 'unsafe', 'partial', 'import',
             'opaque', 'implemented_by', 'extern', 'init_quot', 'addDecl', 'skipKernelTC'}

def sha(data): return hashlib.sha256(data).hexdigest()

def blocked(text, specification=False):
    identifiers = set(re.findall(r"[A-Za-z_][A-Za-z_0-9.']*", text))
    words = FORBIDDEN | ({'by', 'GoldSpec', 'Coverage', 'Nonvacuous', 'Context'} if specification else set())
    return sorted(t for t in words if any(i == t or i.split('.')[-1] == t for i in identifiers))

def context(case, specification):
    assert isinstance(specification, str) and 0 < len(specification.encode()) <= 12000
    if blocked(specification, True): raise ValueError('Forbidden specification syntax')
    gold = (PRIVATE/'cases'/case['id']/'GoldDefinition.txt').read_text()
    assert sha(gold.encode()) == case['gold_definition_sha256']
    slots = case['slots']
    assert len(slots) == 2 and [s['binder'] for s in slots] == ['f0', 'f1']
    ty = ' → '.join('('+s['typePP']+')' for s in slots) + ' → Prop'
    signature = case['signature']
    return ('import SpecOnly\nnamespace Natural\n' + gold + '\n' +
            'specification AgentSpec : '+ty+' := '+json.dumps('fun f0 f1 => '+specification, ensure_ascii=False)+'\n'+
            'def Coverage : Prop := ∀ '+signature+', AgentSpec f0 f1 → GoldSpec f0 f1\n'+
            'def Nonvacuous : Prop := ∃ '+signature+', AgentSpec f0 f1\n'+
            'def Counterexample : Prop := ∃ '+signature+', AgentSpec f0 f1 ∧ ¬ GoldSpec f0 f1\n'+
            'end Natural\n')

class ContextFailure(ValueError):
    def __init__(self, category, message):
        super().__init__(message)
        self.category=category

class Checker:
    def __init__(self, directory, source):
        self.root = Path(directory).resolve()
        self.trusted = self.root/'trusted'
        self.trusted.mkdir(parents=True, exist_ok=True)
        self.env = {k:v for k,v in os.environ.items() if not re.search('KEY|TOKEN|SECRET|PASSWORD|CREDENTIAL|AUTH|COOKIE|SESSION', k, re.I)}
        self.lean = subprocess.check_output(['elan','which','lean'],cwd=LEAN_PROJECT,text=True,env=self.env).strip()
        self.version = subprocess.check_output([self.lean,'--version'],text=True,env=self.env).strip()
        assert '4.22.0' in self.version
        assert (LEAN_PROJECT/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.22.0'
        self.lib = subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=LEAN_PROJECT,text=True,env=self.env).strip().splitlines()[-1]
        self.path = str(self.trusted)+':'+self.lib
        (self.trusted/'SpecOnly.lean').write_text(SPEC_ONLY)
        (self.trusted/'Context.lean').write_text(source)
        for name in ['ProofOnly', 'KernelReplayStrictSupport']:
            shutil.copyfile(DEPENDENCIES/(name+'.lean'), self.trusted/(name+'.lean'))
        self.builds = {}
        for name in ['SpecOnly','Context','ProofOnly','KernelReplayStrictSupport']:
            result = self.compile(self.trusted/(name+'.lean'), self.path, True)
            self.builds[name] = result
            if result['exit_code']:
                category='invalid_context' if name=='Context' and result['exit_code']==1 else 'infrastructure_missing'
                (self.root/'build_failure.json').write_text(json.dumps(self.builds,indent=2)+'\n')
                raise ContextFailure(category,f'{name} failed: '+result['output'][-1800:])
        self.protected = self.hashes()

    def hashes(self):
        return {p.name:sha(p.read_bytes()) for p in self.trusted.iterdir() if p.suffix in {'.lean','.olean'} and not p.name.startswith('Replay_')}

    def compile(self, file, search_path, output=False, isolate=False):
        cmd=[self.lean,'-j1','-DmaxHeartbeats=400000','-DElab.async=false','-R',str(file.parent)]
        if output: cmd += ['-o',str(file.with_suffix('.olean'))]
        cmd.append(str(file))
        if isolate:
            assert Path('/usr/bin/sandbox-exec').exists()
            profile='(version 1)(allow default)(deny network*)(deny file-write*)(allow file-write* (subpath '+json.dumps(str(file.parent.resolve()))+'))'
            cmd=['/usr/bin/sandbox-exec','-p',profile]+cmd
        try:
            p=subprocess.run(cmd,cwd=LEAN_PROJECT,env=dict(self.env,LEAN_PATH=search_path),text=True,capture_output=True,timeout=60)
            return {'exit_code':p.returncode,'output':p.stdout+p.stderr,'argv':cmd,'timeout_seconds':60}
        except subprocess.TimeoutExpired:
            return {'exit_code':124,'output':'Compile time limit 60 seconds','argv':cmd,'timeout_seconds':60}

    def check(self, proof, target):
        if not isinstance(proof,str) or not proof.strip() or len(proof.encode())>20000:
            return {'accepted':False,'status':'invalid_proof_size'}
        rejected=blocked(proof)
        if rejected: return {'accepted':False,'status':'proof_guard_rejected','tokens':rejected}
        source='import Context\nimport ProofOnly\ncandidate claim : '+target+' := '+json.dumps(proof,ensure_ascii=False)+'\n'
        return self.check_raw(source,target)

    def check_raw(self, source, target):
        """Raw declarations are used only by adversarial checker controls, never model output."""
        assert target in {'Natural.Coverage','Natural.Nonvacuous','Natural.Counterexample','Natural.Inconsistent','True','False'}
        assert self.hashes()==self.protected
        directory=Path(tempfile.mkdtemp(prefix='candidate_',dir=self.root))
        candidate=directory/'Candidate.lean'; candidate.write_text(source)
        result={'target':target,'candidate_sha256':sha(source.encode()),'accepted':False}
        compiled=self.compile(candidate,str(directory)+':'+self.path,True,True)
        result['compile']=compiled
        if compiled['exit_code']:
            result['status']='search_timeout' if compiled['exit_code']==124 else 'infrastructure_failure' if compiled['exit_code']<0 else 'proof_rejected'
        else:
            artifact=candidate.with_suffix('.olean'); original=sha(artifact.read_bytes())
            nonce=secrets.token_hex(24)
            replay=self.trusted/('Replay_'+nonce+'.lean')
            replay.write_text('import Context\nimport KernelReplayStrictSupport\n#vb_strict_kernel_replay '+json.dumps(nonce)+' '+json.dumps(str(artifact))+' claim : '+target+'\n')
            try: checked=self.compile(replay,self.path)
            finally: replay.unlink(missing_ok=True)
            records=[]
            for line in checked['output'].splitlines():
                if 'VB169_STRICT_KERNEL_REPLAY_JSON ' in line:
                    try: r=json.loads(line.split('VB169_STRICT_KERNEL_REPLAY_JSON ',1)[1])
                    except json.JSONDecodeError: continue
                    if r.get('nonce')==nonce: records.append(r)
            r=records[0] if len(records)==1 else {}
            result.update({'replay':checked,'records':records,'olean_sha256':original,'olean_unchanged':sha(artifact.read_bytes())==original})
            result['accepted']=bool(checked['exit_code']==0 and r.get('replayed') and r.get('isTheorem') and r.get('typeExact') and not r.get('collisions') and set(r.get('axioms',[]))<=AXIOMS and result['olean_unchanged'])
            result['status']='accepted' if result['accepted'] else 'search_timeout' if checked['exit_code']==124 else 'infrastructure_failure' if checked['exit_code']<0 else 'kernel_replay_rejected'
        result['protected_intact']=self.hashes()==self.protected
        assert result['protected_intact']
        (directory/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
        return result
