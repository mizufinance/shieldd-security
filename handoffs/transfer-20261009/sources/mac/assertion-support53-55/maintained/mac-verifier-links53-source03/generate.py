"""Finite source-only emission; no refresh of a frozen packet."""
from pathlib import Path
import sys,hashlib,re,json
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated nonoptimized Python')
require(not(S/'generation01.json').exists()and not(S/'source-root').exists(),'immutable emission')
p=S/'template.lean';require(pin(p)['sha256']=='c557cc553c3ef7478d904a0300e52c7bcfbc05673f117841b1b5016d520ad55c','exact maintained template before loading')
t=p.read_text();names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M);require(len(names)==12,'closed public inventory')
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.CompilerVerifierLinks53.{n}\n#print axioms ShielddSecurity.CompilerVerifierLinks53.{n}\n'for n in names)
root=S/'source-root/ShielddSecurity';root.mkdir(parents=True);out=root/'CompilerVerifierLinks53.lean'
with out.open('x')as f:f.write(t)
with(S/'generation01.json').open('x')as f:f.write(json.dumps(dict(template=pin(p),generator=pin(Path(__file__)),source=pin(out),audits=['ShielddSecurity.CompilerVerifierLinks53.'+n for n in names],scope='Unrun generic source proposal; actual original verifier rows 200767..200769 bindings remain separately finite provider obligations.'),sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(dict(source=pin(out),planned_audits=len(names))))
