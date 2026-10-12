from pathlib import Path
import sys,json,hashlib,ast,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');old=W/'mac-arithmetic-selection252-source02';S=W/'mac-arithmetic-selection254-source01'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated');require(not S.exists(),'immutable');spec=json.loads((old/'templates01.json').read_bytes());body=spec['modules']['CapturedArithmeticSelection252']['body'];start=body.index('theorem row_selected');end=body.index('theorem copy_position');generic=body[start:end];generic=generic.replace('variable {F : Type} [Field F] [CharP F p]','')
header='''import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerSelectedTruth254
open Compiler CompilerAssertionBlock51
variable {F : Type} [Field F] {p copy : Nat} [CharP F p]
'''
core=header+generic+'end ShielddSecurity.CompilerSelectedTruth254\n'
actual=body[:start]+'''theorem row_selected := @CompilerSelectedTruth254.row_selected
theorem selected_sound := @CompilerSelectedTruth254.selected_sound
'''+body[end:];actual=actual.replace('import ShielddSecurity.CompilerIndexedCopyStream171','import ShielddSecurity.CompilerSelectedTruth254');actual=actual.replace('selected_sound _ _ indices targets checked rho linked','CompilerSelectedTruth254.selected_sound (p:=p) (copy:=copy) _ _ indices targets checked rho linked')
# Alias signatures remain generic; actual candidate theorem fixes captured parameters explicitly.
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'disk');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((old/'generate.py').read_bytes());inputs=spec['inputs'];inputs[str(old/'templates01.json')]=pin(old/'templates01.json');put('templates01.json',dict(modules={'CompilerSelectedTruth254':dict(body=core,names=['row_selected','selected_sound']),'CapturedArithmeticSelection252':dict(body=actual,names=spec['modules']['CapturedArithmeticSelection252']['names'])},inputs=inputs,scope=dict(status='SOURCE_ONLY_UNRUN',failure2255='Concrete-parameter generic selection252 heap refusal preserved; split generic field/p/copy proof away from entire captured provider import',open=['Kernel qualification','legal-input derivations'],runtime=spec['scope']['runtime'],source_context=spec['scope']['source_context'])))
print(str(S))
