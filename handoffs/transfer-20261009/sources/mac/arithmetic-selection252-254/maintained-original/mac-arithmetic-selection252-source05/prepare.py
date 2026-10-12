from pathlib import Path
import sys,json,hashlib,ast
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-arithmetic-selection252-source04';S=W/'mac-arithmetic-selection252-source05'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated');require(not S.exists(),'immutable');spec=json.loads((P/'templates01.json').read_bytes());d=spec['modules']['CapturedArithmeticSelection252'];d['body']=d['body'].replace('open CapturedInitial73419Generic01 (p copy)','open CompilerArithmeticTransport41 (p copy)').replace('theorem row_selected :=','abbrev row_selected :=').replace('theorem selected_sound :=','abbrev selected_sound :=');spec['inputs'][str(P/'templates01.json')]=pin(P/'templates01.json');spec['scope']['repair']='Actual2258 diagnostics reveal missing Initial734 namespace and theorem-alias syntax, not a qualified proof failure. Use already imported exact ArithmeticTransport41 p/copy and transparent audited abbrev aliases; maintain interleaved audit diagnostics.';spec['scope']['prior_failures']=[2255,2257,2258];S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((P/'generate.py').read_bytes());put('templates01.json',spec)
