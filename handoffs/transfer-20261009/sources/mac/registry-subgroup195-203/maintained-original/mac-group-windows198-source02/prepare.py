from pathlib import Path
import json,hashlib,re,sys,ast
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-group-windows198-source02'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');require(not S.exists(),'immutable source')
old=W/'shared-build-handoff/circuits/ShielddSecurity/GroupWindows.lean';body=old.read_text()
require(len(re.findall(r'(?m)^#print axioms [^\n]+\n',body))==9,'exact historical diagnostic inventory')
body=re.sub(r'(?m)^#print axioms [^\n]+\n','',body)
require(body.count('set_option maxHeartbeats 500000')==1 and '#check' not in body,'exact primary header')
body=body.replace('set_option maxHeartbeats 500000','set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192',1)
names=['addition_closure_polynomial','affine_rows_onCurve','identityPoint','shared_inverse_rows','shared_inverse_double_sound','double_rows_sound','identity_onCurve','chooseCoordinate','windowPoint','windowCase','window_correct','window_onCurve','StandardCurveModel','cofactor_image_annihilated','represented_nonidentity']
g=(W/'mac-indexed-slices183-source01/generate.py').read_text();needle="names=['ShielddSecurity.'+module+'.'+n for n in d['names']]";require(g.count(needle)==1,'exact generator name seam')
g=g.replace(needle,"names=d.get('qualified_names',['ShielddSecurity.'+module+'.'+n for n in d['names']])");ast.parse(g)
pins=[W/'mac-group-windows198-source01/producer-manifest01.json',old,W/'mac-group-arithmetic78-source02/source-root/ShielddSecurity/Group.lean']
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_text(g)
(S/'templates01.json').write_text(json.dumps(dict(modules={'GroupWindows':dict(body=body,names=names,qualified_names=['ShielddSecurity.Group.'+n for n in names])},inputs={str(p):pin(p)for p in pins},scope='SOURCE_ONLY_UNRUN fresh Mac qualification proposal of primary GroupWindows bodies. Only explicit finite diagnostic options/audits added; all mathematical bodies preserved. Same Group namespace and qualified locally accepted Group source. Historical Windows qualification not fresh Mac credit. Fifteen planned reports; model and universal group exponent explicit independent premises.'),sort_keys=True,separators=(',',':'))+'\n')
