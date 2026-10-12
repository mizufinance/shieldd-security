from pathlib import Path
import sys,json,hashlib,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');O=W/'mac-canonical-representation219-source01';S=W/'mac-canonical-representation219-source02'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source');require(not S.exists(),'immutable repair');spec=json.loads((O/'templates01.json').read_bytes());d=spec['modules']['CanonicalRepresentation219'];needle='inputs.map fun x => (x:F)';require(d['body'].count(needle)==1,'exact offending Nat-cast lambda');d['body']=d['body'].replace(needle,'inputs.map fun x : Nat => (x:F)')
for f in ['templates01.json','generation01.json','producer-manifest01.json']:spec['inputs'][str(O/f)]=pin(O/f)
p=W/'mac-full-arithmetic45-execution288/runtime/receipts/2356-CanonicalRepresentation219.json';r=json.loads(p.read_bytes());require(r['status']=='failed' and r['exit']==1 and r['cleanup']['clean'],'retained actual failure');spec['inputs'][str(p)]=pin(p);spec['inputs'][r['stdout']['path']]=r['stdout'];spec['scope']=dict(status='SOURCE_ONLY_UNRUN',reports=5,repair='2356 one error: untyped map lambda inferred F; explicit Nat binder restores intended Nat→F cast. All other statements/proofs/names untouched.',open=['All source02 audits UNRUN','Concrete representation/SDK instance/full Transfer'],runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',source_context='cec1b30defc23497c8e9b30528dca12b09d328ea')
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'source disk reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((O/'generate.py').read_bytes());put('templates01.json',spec)
