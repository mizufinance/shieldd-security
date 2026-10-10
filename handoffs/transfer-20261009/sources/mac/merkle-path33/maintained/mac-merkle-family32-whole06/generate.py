from pathlib import Path
import sys,re,json,hashlib
S=Path(__file__).resolve().parent
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def require(x,m):
 if not x:raise ValueError(m)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags')
t=(S/'template.lean').read_text();names=re.findall(r'^\s*(?:def|theorem) (\w+)',t,re.M)
# Abbreviations are private scaffolding namespaces; public proof/constructor names fully audited.
t+='\n'+''.join(f'set_option pp.all true in\n#check @ShielddSecurity.MerkleFamily32Whole.{n}\n#print axioms ShielddSecurity.MerkleFamily32Whole.{n}\n'for n in names)
p=S/'source-root/ShielddSecurity/MerkleFamily32Whole.lean';t+=''.join(f'set_option pp.all true in\n#check @ShielddSecurity.MerkleFamily32Whole.T.{n}\n#print axioms ShielddSecurity.MerkleFamily32Whole.T.{n}\n'for n in ['data0','data1','offset']);b=t.encode();require(len(b)<=262144,'source')
if p.exists():require(p.read_bytes()==b,'immutable replay')
else:
 with p.open('xb')as f:f.write(b)
g=json.dumps(dict(source=pin(p),template=pin(S/'template.lean'),generator=pin(Path(__file__))),sort_keys=True)+'\n'
with (S/'generation01.json').open('x')as f:f.write(g)
print(len(b),len(names))
