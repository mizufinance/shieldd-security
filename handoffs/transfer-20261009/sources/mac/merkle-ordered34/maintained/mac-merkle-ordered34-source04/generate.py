from pathlib import Path
import hashlib,json,sys,re
S=Path(__file__).resolve().parent
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags')
n='MerkleOrdered34';t=(S/'template.lean').read_text();t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.{n}.{x}\n#print axioms ShielddSecurity.{n}.{x}\n'for x in re.findall(r'^\s*(?:def|theorem) (\w+)',t,re.M));p=S/'source-root/ShielddSecurity'/(n+'.lean');p.parent.mkdir(parents=True,exist_ok=True)
with p.open('xb')as f:f.write(t.encode())
with(S/'generation01.json').open('x')as f:json.dump(dict(generator=pin(Path(__file__)),template=pin(S/'template.lean'),source=pin(p)),f,sort_keys=True)
