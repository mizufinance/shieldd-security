from pathlib import Path
import json,hashlib,re,sys
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable emission')
t=(S/'template.lean').read_text();names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M);require(len(names)==len(set(names))==31,'complete31 declarations')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CompilerSubgroupSource80.{n}\n#print axioms ShielddSecurity.CompilerSubgroupSource80.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CompilerSubgroupSource80.lean'
with p.open('x')as f:f.write(t)
put('generation01.json',dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),primary_source=dict(path='/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/shared-build-handoff/circuits/ShielddSecurity/GroupSubgroupSourceGraph.lean',bytes=24590,sha256='4eb9e929d6740b68445fb4e3f1e8873c76868ea116a98ed89e3f03ff01806eba'),source=pin(p),audits=['ShielddSecurity.CompilerSubgroupSource80.'+n for n in names],scope='SOURCE UNRUN. Exact80-node typed source pattern and6 source assertion slots; symbolic evaluation and independent polynomial preimage constructor. Actual captured graph/rows/model/native joins remain OPEN; full legal/native still OPEN. Full legal Transfer/native remain OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(pin(p)))
