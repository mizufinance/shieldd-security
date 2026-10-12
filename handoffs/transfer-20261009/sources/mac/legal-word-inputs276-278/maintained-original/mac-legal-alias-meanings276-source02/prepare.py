from pathlib import Path
import json,hashlib,sys,os,difflib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');A=W/'mac-legal-alias-meanings276-source01';S=W/'mac-legal-alias-meanings276-source02';B=W/'mac-legal-word-encoding278-source01';T=W/'mac-legal-word-encoding278-source02'
def require(v,m):
 if not v:raise RuntimeError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(root,n,v):
 with(root/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags');require(not S.exists()and not T.exists(),'immutable');require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+1048576,'source reserve');d=json.loads((A/'templates01.json').read_bytes());old=d['modules']['LegalAliasMeanings276']['body'];body=old;require(body.count('(number%2:F)')==1,'exact cast error');body=body.replace('(number%2:F)','((number%2:Nat):F)');needle=' rw [BooleanHints207.seeded_selected _ _ _ column (selected column selectedAlias)]\n';require(body.count(needle)==1,'exact seeded seam');body=body.replace(needle,' change BooleanHints207.seeded base (SharedWordWitness221.bits (normalized numbers) (fallback numbers old))\n  SharedWordWitness221.seedColumns column=(normalized numbers column:F)\n'+needle);d['modules']['LegalAliasMeanings276']['body']=body
for p,v in d['inputs'].items():require(pin(Path(p))==v,'unchanged inherited source')
d['inputs'][str(A/'templates01.json')]=pin(A/'templates01.json');d['scope']['repair']='Failed2382 preserved; explicitly Nat-typed modulo before field cast; explicit seeded definitional seam before qualified rewrite. Same intended conclusions/hypotheses, no new row truth/native premise.';S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((A/'generate.py').read_bytes());put(S,'templates01.json',d);(S/'source.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),body.splitlines(True),fromfile=str(A/'templates01.json'),tofile=str(S/'templates01.json'))));print(json.dumps(dict(source=str(S),reports=16)))
