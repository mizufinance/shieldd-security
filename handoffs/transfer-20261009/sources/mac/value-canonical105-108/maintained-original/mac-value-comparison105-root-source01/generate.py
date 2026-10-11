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
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable fresh emission')
t=(S/'template.lean').read_bytes();require(len(t)<262144,'source bound');r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);p=r/'CapturedValueComparison105.lean';p.write_bytes(t)
put('generation01.json',dict(source=pin(p),template=pin(S/'template.lean'),generator=pin(Path(__file__)),audits=['ShielddSecurity.CapturedValueComparison105.'+n for n in ['entries', 'initial', 'actualRows', 'productionCheck', 'production_checked', 'output_exact', 'actual_count', 'selected_satisfies', 'semantic']],scope='Exact508 actual captured comparison product rows composed from8 qualified slices, no desired comparison truth. Characteristic/copy/arithmetic satisfaction soundness interfaces explicit.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(pin(p)))
