from pathlib import Path
import json,sys,re,hashlib
S=Path(__file__).resolve().parent;P=S.parent/'mac-merkle-family32-prefix-remaining01'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
sources=[];missing=[];imports=[]
for level in range(3,17):
 for rd in range(2):
  name=f'MerkleFamily32L{level:02d}R{rd}';p=P/'source-root/ShielddSecurity'/(name+'.lean');t=p.read_text();sources.append(pin(p));imports.append('import ShielddSecurity.'+name)
  declarations=re.findall(r'^\s*(?:def|theorem) (\w+)',t,re.M);existing=re.findall(r'^#check @ShielddSecurity\.'+name+r'\.(\w+)',t,re.M)
  require(len(declarations)==23 and len(existing)==14,'exact historical audit gap')
  missing +=['ShielddSecurity.'+name+'.'+n for n in declarations if n not in existing]
require(len(missing)==252 and len(set(missing))==252,'exact supplemental names')
t='\n'.join(imports)+'\n-- Audit-only immutable imports: no accepted proof/module replay.\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\n'
t+=''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in missing)
b=t.encode();p=S/'source-root/ShielddSecurity/MerkleFamily32Audit.lean'
if p.exists():require(p.read_bytes()==b,'immutable audit replay')
else:
 with p.open('xb')as f:f.write(b)
d=dict(generator=pin(Path(__file__)),sources=sources,missing=missing,output=pin(p));p=S/'generation01.json';b=(json.dumps(d,sort_keys=True)+'\n').encode()
if p.exists():require(p.read_bytes()==b,'immutable metadata')
else:
 with p.open('xb')as f:f.write(b)
print(json.dumps(dict(audits=len(missing),source_bytes=len(t.encode()))))
