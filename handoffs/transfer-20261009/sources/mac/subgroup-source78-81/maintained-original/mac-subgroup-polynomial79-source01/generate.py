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
t=(S/'template.lean').read_text();names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M);require(len(names)==len(set(names))==25,'complete25 declarations')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CompilerSubgroupArithmetic79.{n}\n#print axioms ShielddSecurity.CompilerSubgroupArithmetic79.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CompilerSubgroupArithmetic79.lean'
with p.open('x')as f:f.write(t)
put('generation01.json',dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),primary_source=dict(path='/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/shared-build-handoff/circuits/ShielddSecurity/GroupSubgroupGraphArithmetic.lean',bytes=9710,sha256='1359ddcf0e5b2a418b071941580783aa939cf2d051f9394d4cc4286ebaa91df0'),source=pin(p),audits=['ShielddSecurity.CompilerSubgroupArithmetic79.'+n for n in names],scope='SOURCE UNRUN. Pure field seven-node curve/seventeen-node double/three-step recurrence; independent preimage and finite nonzero denominators construct source-polynomial assertions; operation joined to qualified Group.affineAdd. Actual captured-row/sourcegraph/model/native joins remain OPEN; full legal/native still OPEN. Full legal Transfer/native remain OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(pin(p)))
