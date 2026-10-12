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
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);t=(S/'template.lean').read_text();audits=['ShielddSecurity.CapturedRegistryGlobalSound176.'+n for n in ['row_families','hash']]
t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in audits);require(len(t.encode())<=262144,'finite source');p=r/'CapturedRegistryGlobalSound176.lean';p.write_text(t)
put('generation01.json',dict(outputs=[dict(name='CapturedRegistryGlobalSound176',source=pin(p),audits=audits)],generator=pin(Path(__file__)),template=pin(S/'template.lean'),scope='SOURCE-only arbitrary-assignment nested registry hash under full200770 captured relation and rho0=1. All local row truth is derived by finite indexed coverage; no desired hash, initial-row truth, or source-caller premise. All dependencies must qualify before this module. Constructor remains1467 assertions; native/fulllegalTransfer OPEN.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(source=pin(p),audits=len(audits))))
