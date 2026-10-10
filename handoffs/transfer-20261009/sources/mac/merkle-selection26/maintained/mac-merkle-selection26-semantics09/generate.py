from pathlib import Path
import re,sys,hashlib,json
if not(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize):raise ValueError('isolated flags')
S=Path(__file__).resolve().parent;t=(S/'semantic-template.lean.txt').read_text();names=re.findall(r'^(?:def|theorem) (\w+)',t,re.M)
# Small alias namespace D is private API shorthand; audit it with exact qualification.
a=["D.rows","D.left","D.right","D.outputs"]
for n in names:a.append(n)
b=(t+'\n'+''.join('set_option pp.all true in\n#check @ShielddSecurity.MerkleSelection26Semantic.'+n+'\n#print axioms ShielddSecurity.MerkleSelection26Semantic.'+n+'\n'for n in a)).encode();p=S/'source-root/ShielddSecurity/MerkleSelection26Semantic.lean'
if p.exists():
 if p.read_bytes()!=b:raise ValueError('immutable mismatch')
else:
 with p.open('xb')as f:f.write(b)
print(json.dumps(dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),audits=len(a))))
