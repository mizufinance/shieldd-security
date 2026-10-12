from pathlib import Path
import json,hashlib,sys,runpy
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution280';S=W/'mac-indexed-candidate260-source01'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated');require(not S.exists(),'immutable');g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_ONLY');c=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);q=json.loads(Path(c['closure']['path']).read_bytes())['modules'];q.update(c['qualified_batch_imports']);v=q['CompilerIndexedCopySelection166']['source'];require(pin(Path(v['path']))==v,'qualified original166');raw=Path(v['path']).read_text();a=raw.index('theorem sound');b=raw.index('end ShielddSecurity.CompilerIndexedCopySelection166',a);core=raw[a:b].replace('theorem sound','theorem selected_sound');needle='(satisfied : SatisfiesAt rho parent fullLength)';require(core.count(needle)==1,'exact parent truth binder');core=core.replace(needle,'(truth : ∀ position∈indices,∀ actual,parent position=some actual → Square (eval rho actual.a) (eval rho actual.b))').replace('have row:=satisfied position facts.1 actual actualFound','have row:=truth position (List.mem_of_getElem? selected) actual actualFound');body='''import ShielddSecurity.CompilerIndexedCopySelection166
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerIndexedTruth260
open Compiler CompilerAssertionBlock51 CompilerIndexedCopySelection166
variable {F : Type} [Field F] {p : Nat} [CharP F p]
'''+core+'end ShielddSecurity.CompilerIndexedTruth260\n'
actual='''import ShielddSecurity.CompilerIndexedTruth260
import ShielddSecurity.CapturedArithmeticSelection252
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedIndexedCandidate260
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) (indices : List Nat) (targets : List Row)
 (checked : CompilerIndexedCopySelection166.check p copy CapturedFullRelation58.rowAt 200770 indices targets=true)
 (supports : ∀ index∈indices,CapturedArithmeticSelection252.Supported index) :
 Satisfies (CapturedFullRelation58.candidate base) targets :=
 CompilerIndexedTruth260.selected_sound copy _ _ indices targets checked _
   (CapturedFullRelation58.candidate_links base).2.2
   (fun index member row found => CapturedArithmeticSelection252.supported_row _
     (CapturedFullRelation58.candidate_arithmetic base) (CapturedFullRelation58.candidate_links base).2.2
     index (supports index member) row found)
end ShielddSecurity.CapturedIndexedCandidate260
''';inputs={v['path']:v};v=q['CapturedArithmeticSelection252']['source'];inputs[v['path']]=v;S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-merkle-sparse243-source02/generate.py').read_bytes());put('templates01.json',dict(modules={'CompilerIndexedTruth260':dict(body=body,names=['selected_sound']),'CapturedIndexedCandidate260':dict(body=actual,names=['rows'])},inputs=inputs,scope=dict(status='SOURCE_ONLY_UNRUN',goal='Reuse existing indexed canonical checker166 with truth only at selected owned arithmetic/copy positions, no FullSAT/target-row/hash premise',open=['Kernel qualification','actual component wrappers','legal seed/all assertions/native'],runtime=c['runtime_sha'],source_context=c['canonical_context'])))
