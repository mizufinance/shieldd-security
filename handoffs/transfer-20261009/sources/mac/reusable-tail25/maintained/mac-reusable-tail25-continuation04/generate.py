from pathlib import Path
import re,sys,json,hashlib
if not(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize):raise ValueError('isolated flags')
S=Path(__file__).resolve().parent
for file,name,ns in [('wide-template.lean.txt','ReusableWideTail25','ReusableWideTail25')]:
 t=(S/file).read_text();names=re.findall(r'^(?:def|theorem) (\w+)',t,re.M)
 b=(t+'\n'+''.join('set_option pp.all true in\n#check @ShielddSecurity.'+ns+'.'+n+'\n#print axioms ShielddSecurity.'+ns+'.'+n+'\n' for n in names)).encode();p=S/'source-root/ShielddSecurity'/(name+'.lean')
 if p.exists():
  if p.read_bytes()!=b:raise ValueError('immutable mismatch')
 else:
  with p.open('xb') as f:f.write(b)
 print(json.dumps(dict(module=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),audits=len(names))))
