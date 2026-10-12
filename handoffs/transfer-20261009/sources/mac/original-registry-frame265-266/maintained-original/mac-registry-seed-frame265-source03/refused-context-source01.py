from pathlib import Path
import json,hashlib,sys,os,re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');O=W/'mac-registry-seed-frame265-source02';S=W/'mac-registry-seed-frame265-source03';P=W/'mac-full-arithmetic45-execution294'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source');require(not S.exists(),'immutable');spec=json.loads((O/'templates01.json').read_bytes());d=spec['modules']['RegistrySeedFrame265'];body=d['body'];require(len(re.findall(r'\bprotected\b',body))==8,'exact reserved binder occurrences');d['body']=re.sub(r'\bprotected\b','preserved',body);spec['modules']={'RegistrySeedFrame265':d}
for f in ['templates01.json','generation01.json','producer-manifest01.json']:spec['inputs'][str(O/f)]=pin(O/f)
rp=P/'runtime/receipts/2374-RegistrySeedFrame265.json';r=json.loads(rp.read_bytes());require(r['status']=='failed'and r['exit']==1 and r['cleanup']['clean'],'actual syntax failure');spec['inputs'][str(rp)]=pin(rp);spec['inputs'][r['stdout']['path']]=r['stdout'];sp=P/'runtime/receipts/2373-SharedSeedShape265.json';accepted=json.loads(sp.read_bytes());require(accepted['status']=='passed'and accepted['cleanup']['clean'],'opaque shape accepted');spec['inputs'][str(sp)]=pin(sp);spec['inputs'][accepted['source']['path']]=accepted['source'];spec['scope']['repair']='2374 parser rejected reserved binder protected. Rename binder only to preserved; all conclusions and proof operations unchanged.11 accepted shape modules reused without generation/replay.';spec['scope']['reports']=6
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'source reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((O/'generate.py').read_bytes());put('templates01.json',spec)
