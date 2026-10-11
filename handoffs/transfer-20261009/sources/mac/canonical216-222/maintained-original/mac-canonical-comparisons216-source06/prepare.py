from pathlib import Path
import json,hashlib,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-canonical-comparisons216-source03';S=W/'mac-canonical-comparisons216-source06'
def require(c,m):
 if not c:raise RuntimeError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');require(not S.exists(),'fresh immutable maintained successor')
m=json.loads((P/'producer-manifest01.json').read_bytes());tp=P/'templates01.json';require(pin(tp)==m['templates01.json'],'exact old maintained template');v=json.loads(tp.read_bytes());d=v['modules']['CanonicalComparisonSlices218'];require(d['body'].startswith('import ShielddSecurity.CompilerRowSlice63\n'),'exact old import seam');body='import ShielddSecurity.CapturedFullArithmetic52\n'+d['body'];v['modules']={'CanonicalComparisonSlices218':dict(body=body,names=d['names'])};v['inputs'][str(tp)]=pin(tp);v['inputs'][str(P/'producer-manifest01.json')]=pin(P/'producer-manifest01.json');v['scope']='Maintained import-only helper repair: explicitly import qualified full arithmetic row provider. Entire failed1244 helper preserved unqualified; no semantic statement change.'
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
