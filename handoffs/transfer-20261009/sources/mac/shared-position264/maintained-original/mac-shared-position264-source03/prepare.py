from pathlib import Path
import sys,json,hashlib,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');O=W/'mac-shared-position264-source02';S=W/'mac-shared-position264-source03'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source');require(not S.exists(),'immutable repair');spec=json.loads((O/'templates01.json').read_bytes());d=spec['modules']['SharedMerklePosition264']
changes=[("by rfl⟩","by change 184+i.val=184+1*i.val; simp only [Nat.one_mul]⟩")]
for old,new in changes:
 require(d['body'].count(old)==1,'exact proof repair context');d['body']=d['body'].replace(old,new)
for f in ['templates01.json','generation01.json','producer-manifest01.json']:spec['inputs'][str(O/f)]=pin(O/f)
p=W/'mac-full-arithmetic45-execution291/runtime/receipts/2360-SharedMerklePosition264.json';r=json.loads(p.read_bytes());require(r['status']=='failed' and r['exit']==1 and r['cleanup']['clean'] and r['cleanup']['leader_reaped'],'actual preserved failure');spec['inputs'][str(p)]=pin(p);spec['inputs'][r['stdout']['path']]=r['stdout'];spec['scope']['repair']='2360 single membership witness error: reduce concrete slot.start with change, then normalize Nat.one_mul. All other source02 statements/proofs/names unchanged.'
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'source disk reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((O/'generate.py').read_bytes());put('templates01.json',spec)
