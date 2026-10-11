from pathlib import Path
import sys,hashlib,re,json
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated nonoptimized flags')
require(not(S/'generation01.json').exists()and not(S/'source-root').exists(),'immutable emission')
p=S/'template.lean';require(pin(p)['sha256']=='b6979e42c196b4dd528da8206178754ba659c04d53b57944e0b81a914bf9713b','exact template before loading');t=p.read_text();names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M);require(len(names)==5,'exact public inventory')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CompilerAssertionPairs55.{n}\n#print axioms ShielddSecurity.CompilerAssertionPairs55.{n}\n'for n in names)
root=S/'source-root/ShielddSecurity';root.mkdir(parents=True);out=root/'CompilerAssertionPairs55.lean'
with out.open('x')as f:f.write(t)
with(S/'generation01.json').open('x')as f:f.write(json.dumps(dict(template=pin(p),generator=pin(Path(__file__)),source=pin(out),audits=['ShielddSecurity.CompilerAssertionPairs55.'+n for n in names],scope='UNRUN; same checkRow production Boolean, sequential pair traversal and symbolic append; no assumed row truth.'),sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(dict(source=pin(out),planned_audits=len(names))))
