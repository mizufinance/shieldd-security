from pathlib import Path
import sys,json,hashlib,re
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'generation01.json').exists() and not(S/'source-root').exists(),'immutable emission')
t=(S/'template.lean').read_text();names=re.findall(r'^(?:noncomputable )?(?:local )?(?:def|theorem|instance) (\w+)',t,re.M)
require(len(names)==24 and len(set(names))==23,'complete unique public inventory')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CapturedEpochNonzero61.{n}\n#print axioms ShielddSecurity.CapturedEpochNonzero61.{n}\n'for n in names)
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CapturedEpochNonzero61.lean'
with p.open('x')as f:f.write(t)
with(S/'generation01.json').open('x')as f:f.write(json.dumps(dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),source=pin(p),audits=['ShielddSecurity.CapturedEpochNonzero61.'+n for n in names],scope='SOURCE only; all24 audits UNRUN. Exact local arithmetic rows256..261 and assertion IDs90..93/global178044..178047. Soundness from those actual rows plus explicit zero/copy. Independent zero/inverse hint seeding requires only regulated-epoch guard. Primitive-to-assertion completeness separately requires constructed arithmetic satisfaction. No full Transfer/native/compiler graph refinement claim.'),sort_keys=True,separators=(',',':'))+'\n')
print(pin(p))
