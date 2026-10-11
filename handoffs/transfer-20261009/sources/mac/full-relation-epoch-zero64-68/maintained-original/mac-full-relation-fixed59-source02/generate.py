from pathlib import Path
import sys,json,hashlib,re
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'generation01.json').exists() and not(S/'source-root').exists(),'immutable emission')
t=(S/'template.lean').read_text();names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M)
require(len(names)==5,'complete declaration inventory')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CapturedRelationFixed59.{n}\n#print axioms ShielddSecurity.CapturedRelationFixed59.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CapturedRelationFixed59.lean'
with p.open('x')as f:f.write(t)
with(S/'generation01.json').open('x')as f:f.write(json.dumps(dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),source=pin(p),audits=['ShielddSecurity.CapturedRelationFixed59.'+n for n in names],scope='SOURCE only, all five audits UNRUN. Full indexed satisfying assignments fix the arithmetic/link candidate and are uniquely determined on compiler columns by initial values. No legal-input assertion truth or native/full Transfer conclusion.'),sort_keys=True,separators=(',',':'))+'\n')
print(pin(p))
