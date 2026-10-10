from pathlib import Path
import sys,re,hashlib,json
S=Path(__file__).resolve().parent
def require(x,m):
 if not x:raise ValueError(m)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
t=(S/'control-template.lean.txt').read_text();names=re.findall(r'^(?:def|theorem) (\w+)',t,re.M);t+='\n'+''.join('set_option pp.all true in\n#check @ShielddSecurity.MerkleHash27Controls.'+n+'\n#print axioms ShielddSecurity.MerkleHash27Controls.'+n+'\n'for n in names);p=S/'source-root/ShielddSecurity/MerkleHash27Controls.lean';b=t.encode()
if p.exists():require(p.read_bytes()==b,'immutable replay')
else:
 with p.open('xb')as f:f.write(b)
print(json.dumps(dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),audits=len(names))))
