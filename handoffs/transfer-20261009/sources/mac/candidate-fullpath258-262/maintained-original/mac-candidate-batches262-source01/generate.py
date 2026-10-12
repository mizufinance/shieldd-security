from pathlib import Path
import sys,json,hashlib
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'source-root').exists()and not(S/'producer-manifest01.json').exists(),'immutable generation')
spec=json.loads((S/'templates01.json').read_bytes())
for p,v in spec['inputs'].items():require(pin(Path(p))==v,'exact source input '+p)
outputs=[]
for module,d in spec['modules'].items():
 names=['ShielddSecurity.'+(n if d.get('qualified_audits') else module+'.'+n) for n in d['names']]
 text=d['body']+'\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in names)
 require(len(text.encode())<=262144 and text.count('set_option maxHeartbeats 900000')==1 and text.count('set_option maxRecDepth 8192')==1,'bounded source')
 p=S/('source-root/ShielddSecurity/'+module+'.lean');p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x')as f:f.write(text)
 outputs.append(dict(name=module,source=pin(p),audits=names))
put('generation01.json',dict(outputs=outputs,generator=pin(Path(__file__)),templates=pin(S/'templates01.json'),scope=spec['scope'],inputs=spec['inputs']))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()})
put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')))
put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(modules=len(outputs),source_bytes=sum(o['source']['bytes']for o in outputs))))
