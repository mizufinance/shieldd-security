from pathlib import Path
import sys,json,re,hashlib
S=Path(__file__).resolve().parent
def require(x,m):
 if not x:raise ValueError(m)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
p=S/'selected-data01.json';b=p.read_bytes();require(hashlib.sha256(b).hexdigest()=='606b3d4d13001937dc5dfde922ec961b9b342b4b99012793cdb93baad9bc98d2','immutable actual data');d=json.loads(b)
for k in ['sidecar','primary_source','census']:
 q=Path(d[k]['path']);v=q.read_bytes();require(len(v)==d[k]['bytes']and hashlib.sha256(v).hexdigest()==d[k]['sha256'],'input pin')
def lin(x):return '['+','.join('('+str(c)+','+str(v)+')'for c,v in x)+']'
t=(S/'bits-template.lean.txt').read_text();require(t.count('@ROWS@')==1,'placeholder');t=t.replace('@ROWS@','['+','.join('⟨'+lin(x['a'])+','+lin(x['b'])+'⟩'for x in d['rows'])+']');names=re.findall(r'^(?:def|theorem) (\w+)',t,re.M);t+='\n'+''.join('set_option pp.all true in\n#check @ShielddSecurity.MerkleBits29.'+n+'\n#print axioms ShielddSecurity.MerkleBits29.'+n+'\n'for n in names);b=t.encode();p=S/'source-root/ShielddSecurity/MerkleBits29.lean'
if p.exists():require(p.read_bytes()==b,'immutable replay')
else:
 with p.open('xb')as f:f.write(b)
print(json.dumps(dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),audits=len(names))))
