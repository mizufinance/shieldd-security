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
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable emission')
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);t=(S/'template.lean').read_text();audits=['ShielddSecurity.CapturedCall04GlobalBinding167Pilot.'+n for n in ['rows','indices','productionCheck','checked','count','sound']]
t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in audits);require(len(t.encode())<=262144,'finite source');p=r/'CapturedCall04GlobalBinding167Pilot.lean';p.write_text(t)
put('generation01.json',dict(outputs=[dict(name='CapturedCall04GlobalBinding167Pilot',source=pin(p),audits=audits)],generator=pin(Path(__file__)),template=pin(S/'template.lean'),scope='First32 actual original Call04 arithmetic positions322..353 transport through exact indexed canonical/copy checks to retained SOURCE19 callRows. No desired local row/hash truth premise. Pilot only; full734/Call04/Merkle/global semantic coverage remains OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(source=pin(p),audits=len(audits))))
