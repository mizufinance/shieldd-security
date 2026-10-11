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
t=(S/'template.lean').read_text();names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M);require(len(names)==len(set(names))==7,'complete7 declarations')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CompilerCoordinateZero69.{n}\n#print axioms ShielddSecurity.CompilerCoordinateZero69.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CompilerCoordinateZero69.lean'
with p.open('x')as f:f.write(t)
put('generation01.json',dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),source=pin(p),audits=['ShielddSecurity.CompilerCoordinateZero69.'+n for n in names],scope='SOURCE UNRUN. Generic coordinate-pair zero guards with canonical-coordinate transport; no actual-row instance claimed. Full legal Transfer/native remain OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(pin(p)))
