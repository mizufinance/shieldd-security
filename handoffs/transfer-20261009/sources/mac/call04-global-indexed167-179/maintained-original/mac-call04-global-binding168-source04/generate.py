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
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);outputs=[]
for name in ['CapturedCall04GlobalBinding168C00', 'CapturedCall04GlobalBinding168C01', 'CapturedCall04GlobalBinding168C02', 'CapturedCall04GlobalBinding168C03', 'CapturedCall04GlobalBinding168C04', 'CapturedCall04GlobalBinding168C05', 'CapturedCall04GlobalBinding168C06', 'CapturedCall04GlobalBinding168C07', 'CapturedCall04GlobalBinding168C08', 'CapturedCall04GlobalBinding168C09', 'CapturedCall04GlobalBinding168C10', 'CapturedCall04GlobalBinding168C11', 'CapturedCall04GlobalBinding168C12', 'CapturedCall04GlobalBinding168C13', 'CapturedCall04GlobalBinding168C14', 'CapturedCall04GlobalBinding168C15', 'CapturedCall04GlobalBinding168C16', 'CapturedCall04GlobalBinding168C17', 'CapturedCall04GlobalBinding168']:
 t=(S/(name+'.template.lean')).read_text()
 names=['count','partition','sound'] if name=='CapturedCall04GlobalBinding168' else ['rows','indices','productionCheck','checked','count','sound']
 audits=['ShielddSecurity.'+name+'.'+n for n in names]
 t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in audits)
 require(len(t.encode())<=262144,'finite source');p=r/(name+'.lean');p.write_text(t)
 outputs.append(dict(name=name,source=pin(p),audits=audits))
put('generation01.json',dict(outputs=outputs,generator=pin(Path(__file__)),templates={p.name:pin(p) for p in S.glob('*.template.lean')},scope='Complete412 original Call04 positions322..733, using passed first32 pilot plus three qualified32-row pieces plus eighteen16-row-or-smaller canonical/copy certificates; failed128/32-row predecessors zero. Full captured relation is sole row antecedent. No supplied hash/initial satisfaction truth; other global semantic families remain OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(outputs=outputs,audits=sum(len(o['audits']) for o in outputs))))
