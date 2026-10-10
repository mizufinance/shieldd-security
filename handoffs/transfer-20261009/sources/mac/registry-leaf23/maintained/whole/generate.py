"""Handwritten mathematical template with maintained exact audit emission."""
from pathlib import Path
import re,sys,hashlib,json
if not (sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize):raise ValueError('require isolated nonoptimized')
S=Path(__file__).resolve().parent;t=(S/'registry-whole-template.lean.txt').read_text();names=re.findall(r'^(?:def|theorem) (\w+)',t,re.M)
b=(t+'\n'+''.join('set_option pp.all true in\n#check @ShielddSecurity.RegistryWhole23.'+n+'\n#print axioms ShielddSecurity.RegistryWhole23.'+n+'\n' for n in names)).encode();p=S/'source-root/ShielddSecurity/RegistryWhole23.lean'
if p.exists():
 if p.read_bytes()!=b:raise ValueError('immutable mismatch')
else:
 with p.open('xb')as f:f.write(b)
print(json.dumps(dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),audits=len(names))))
