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
for name in ['CapturedPriorGlobalBinding170']:
 t=(S/(name+'.template.lean')).read_text()
 names=['headRows','count','chunks','partition','prior_partition','head_sound','sound'] if name=='CapturedPriorGlobalBinding170' else ['rows','indices','productionCheck','checked','count','sound']
 audits=['ShielddSecurity.'+name+'.'+n for n in names]
 t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in audits)
 require(len(t.encode())<=262144,'finite source');p=r/(name+'.lean');p.write_text(t)
 outputs.append(dict(name=name,source=pin(p),audits=audits))
put('generation01.json',dict(outputs=outputs,generator=pin(Path(__file__)),templates={p.name:pin(p) for p in S.glob('*.template.lean')},scope='SOURCE-only exact ordered integer/copy packing coverage. Qualified pilot reused without replay; renamed repaired root UNRUN; five original leaves qualified and reused without replay. Finite captured-row equality derives each target only from full200770 indexed relation, no local/hash truth premise. Prior0..321 plus qualified Call04322..733 yields prior734. Shared constructor1467 unchanged; fullnative/legalTransfer OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(outputs=outputs,audits=sum(len(o['audits']) for o in outputs))))
