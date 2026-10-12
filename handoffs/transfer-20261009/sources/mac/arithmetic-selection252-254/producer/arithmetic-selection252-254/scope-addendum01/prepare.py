from pathlib import Path
import json,hashlib,sys
S=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-arithmetic-selection252-254-kernel-result01')
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(p,v):
 with p.open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
if not(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize):raise ValueError('isolated')
original={str(S/n):pin(S/n)for n in ['producer-manifest01.json','envelope01.json','postseal-guard01.json','ledger-prefix01.json']};v=json.loads((S/'ledger-prefix01.json').read_bytes());last=v['events'][-1]['receipt'];r=json.loads(Path(last['path']).read_bytes());
if r['module']!='CapturedArithmeticSelection252' or r['all_attempts']!=2259 or len(v['events'])!=2:raise ValueError('exact selected prefix')
A=S/'scope-addendum01';A.mkdir();(A/'prepare.py').write_bytes(Path(__file__).read_bytes());put(A/'correction01.json',dict(original=original,correct_prefix_scope='Immutable execution277 two-event prefix ending2259 CapturedArithmeticSelection252; generic254 inherited original2256. Later2260 warning-failed helper preserved separately.',old_scope_string='Only balanced immutable ledger prefix ending at GlobalLevel185L02; later jobs may append',classification='Copied sealer scope-label extraction defect only; no original entry/byte or mathematical claim modified',receipt=last,raw_reports=11,selected_modules=2));put(A/'binding-manifest01.json',{str(p.relative_to(A)):pin(p)for p in A.iterdir()if p.is_file()});print(json.dumps(pin(A/'binding-manifest01.json')))
