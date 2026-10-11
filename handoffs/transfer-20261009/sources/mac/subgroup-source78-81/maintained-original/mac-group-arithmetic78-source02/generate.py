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
t=(S/'template.lean').read_text();names=re.findall(r'^(?:noncomputable )?(?:def|theorem|structure) (\w+)',t,re.M);require(len(names)==len(set(names))==12,'complete12 declarations')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.Group.{n}\n#print axioms ShielddSecurity.Group.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'Group.lean'
with p.open('x')as f:f.write(t)
put('generation01.json',dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),original_primary=dict(path='/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/shared-build-handoff/circuits/ShielddSecurity/Group.lean',bytes=5687,sha256='f0e46677fc91f3705f5c409f4d94f2c871eaf35ee3288e54cf897eb648d1d270'),source=pin(p),audits=['ShielddSecurity.Group.'+n for n in names],scope='SOURCE UNRUN. Exact primary Group arithmetic bodies under finite options/complete12 audit pairs; one compiler-reported unused simp argument removed from affine_rows_sound; no concrete model or native refinement; full legal/native still OPEN. Full legal Transfer/native remain OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(pin(p)))
