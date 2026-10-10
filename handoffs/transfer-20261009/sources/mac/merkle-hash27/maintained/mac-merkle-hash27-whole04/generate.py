from pathlib import Path
import json,re,hashlib,sys
S=Path(__file__).resolve().parent
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
d=json.loads((S/'actual-result-data01.json').read_bytes())
for q in d['primary_sources']:require(pin(Path(q['path']))==q,'actual source pin')
t=(S/'whole-template.lean.txt').read_text();require(t.count('@ACTUAL@')==1,'exact data placeholder');t=t.replace('@ACTUAL@','['+','.join('('+str(c)+','+str(v)+')'for c,v in d['terms'])+']');names=re.findall(r'^(?:def|theorem) (\w+)',t,re.M);t+='\n'+''.join('set_option pp.all true in\n#check @ShielddSecurity.MerkleHash27Whole.'+n+'\n#print axioms ShielddSecurity.MerkleHash27Whole.'+n+'\n'for n in names);p=S/'source-root/ShielddSecurity/MerkleHash27Whole.lean';b=t.encode()
if p.exists():require(p.read_bytes()==b,'immutable byte replay')
else:
 with p.open('xb')as f:f.write(b)
print(json.dumps(dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),audits=len(names))))
