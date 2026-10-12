from pathlib import Path
import json,hashlib,sys,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');O=W/'mac-original-anchor266-source01';S=W/'mac-original-anchor266-source02';N=W/'mac-registry-seed-frame265-source03'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source');require(not S.exists(),'immutable');spec=json.loads((O/'templates01.json').read_bytes());spec['inputs']={p:v for p,v in spec['inputs'].items()if '/mac-registry-seed-frame265-source01/'not in p}
for f in ['templates01.json','generation01.json','producer-manifest01.json']:spec['inputs'][str(O/f)]=pin(O/f)
for f in ['generation01.json','producer-manifest01.json']:spec['inputs'][str(N/f)]=pin(N/f)
for v in json.loads((N/'generation01.json').read_bytes())['outputs']:require(pin(v['source']['path'])==v['source'],'new frame source pin');spec['inputs'][v['source']['path']]=v['source']
spec['scope']['repair']='Only dependency provenance rebinds to repaired265 frame source03; mathematical body and both statements exact source01 bytes. Frame remains UNRUN at preparation.'
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'source reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((O/'generate.py').read_bytes());put('templates01.json',spec)
