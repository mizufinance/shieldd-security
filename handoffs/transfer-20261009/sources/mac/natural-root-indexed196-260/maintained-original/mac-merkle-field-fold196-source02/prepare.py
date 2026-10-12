from pathlib import Path
import sys,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-merkle-field-fold196-source01';S=W/'mac-merkle-field-fold196-source02'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated');require(not S.exists(),'immutable');spec=json.loads((P/'templates01.json').read_bytes());d=spec['modules']['MerkleFieldFold196'];require(d['body'].count('theorem fold_congr')==1,'exact generic lemma');d['body']=d['body'].replace('theorem fold_congr','omit [Field F] in\ntheorem fold_congr');spec['inputs'][str(P/'templates01.json')]=pin(P/'templates01.json');target=W/'mac-merkle-integer-root191-source02/source-root/ShielddSecurity/CapturedMerkleIntegerRoot191.lean';spec['inputs']={p:v for p,v in spec['inputs'].items()if not p.endswith('/CapturedMerkleIntegerRoot191.lean')};spec['inputs'][str(target)]=pin(target);spec['scope']=dict(historical_scope=spec['scope'],repair='2273 exit0/std reports but rejected unused Field premise warning; omit unnecessary field structure from purely symbolic fold_congr',status='SOURCE_ONLY_UNRUN');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(spec,sort_keys=True,separators=(',',':'))+'\n')
