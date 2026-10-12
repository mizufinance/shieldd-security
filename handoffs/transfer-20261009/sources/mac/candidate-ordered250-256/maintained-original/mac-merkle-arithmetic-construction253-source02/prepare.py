from pathlib import Path
import sys,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-merkle-arithmetic-construction253-source01';S=W/'mac-merkle-arithmetic-construction253-source02'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated');require(not S.exists(),'immutable');spec=json.loads((P/'templates01.json').read_bytes());d=spec['modules']['MerkleArithmeticConstruction253'];require(d['body'].count('theorem candidate_zero')==1,'exact declaration');d['body']=d['body'].replace('theorem candidate_zero','omit [CharP F p] in\ntheorem candidate_zero');spec['inputs'][str(P/'templates01.json')]=pin(P/'templates01.json');target=W/'mac-arithmetic-selection252-source05/source-root/ShielddSecurity/CapturedArithmeticSelection252.lean';spec['inputs']={p:v for p,v in spec['inputs'].items()if not p.endswith('/CapturedArithmeticSelection252.lean')};spec['inputs'][str(target)]=pin(target);spec['scope']['repair']='2260 exit0 with unused CharP premise warning; reject entire attempted helper, omit unnecessary premise in new source';S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(spec,sort_keys=True,separators=(',',':'))+'\n')
