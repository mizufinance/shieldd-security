from pathlib import Path
import json,hashlib,sys,runpy
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution279';S=W/'mac-packed-candidate257-source01'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated');require(not S.exists(),'immutable');g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_ONLY');c=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);q=json.loads(Path(c['closure']['path']).read_bytes())['modules'];q.update(c['qualified_batch_imports']);v=q['CompilerIndexedCopyConstant178']['source'];require(pin(Path(v['path']))==v,'exact qualified pack source');raw=Path(v['path']).read_text();a=raw.index('theorem row_sound');b=raw.index('end ShielddSecurity.CompilerIndexedCopyConstant178',a);core=raw[a:b].replace('theorem row_sound','theorem row_selected').replace('theorem sound','theorem selected_sound').replace('row_sound copy','row_selected copy')
needle='(satisfied : SatisfiesAt rho parent fullLength) :';require(core.count(needle)==2,'two exact parent-truth binders');core=core.replace(needle,'(truth : ∀ actual,parent position=some actual → Square (eval rho actual.a) (eval rho actual.b)) :',1);core=core.replace(needle,'(truth : ∀ position∈indices,∀ actual,parent position=some actual → Square (eval rho actual.a) (eval rho actual.b)) :',1);core=core.replace('have row:=satisfied position facts.1 actual actualFound','have row:=truth actual actualFound').replace('target checks.1 rho linked satisfied','target checks.1 rho linked (truth position (List.mem_cons_self ..))').replace('have later:=ih rest checks.2','have later:=ih rest checks.2 (fun i h => truth i (List.mem_cons_of_mem _ h))')
body='''import ShielddSecurity.CompilerIndexedCopyConstant178
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerPackedTruth257
open Compiler CompilerAssertionBlock51 CompilerIndexedCopyConstant178
variable {F : Type} [Field F]
'''+core+'end ShielddSecurity.CompilerPackedTruth257\n'
actual='''import ShielddSecurity.CompilerPackedTruth257
import ShielddSecurity.CapturedArithmeticSelection252
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedPackedCandidate257
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) (indices : List Nat) (targets : List Row)
 (checked : CompilerIndexedCopyConstant178.check copy CapturedFullRelation58.rowAt 200770 indices targets=true)
 (supports : ∀ index∈indices,CapturedArithmeticSelection252.Supported index) :
 Satisfies (CapturedFullRelation58.candidate base) targets :=
 CompilerPackedTruth257.selected_sound copy _ _ indices targets checked _
   (CapturedFullRelation58.candidate_links base).2.2
   (fun index member row found => CapturedArithmeticSelection252.supported_row _
     (CapturedFullRelation58.candidate_arithmetic base) (CapturedFullRelation58.candidate_links base).2.2
     index (supports index member) row found)
end ShielddSecurity.CapturedPackedCandidate257
'''
inputs={v['path']:v};v=q['CapturedArithmeticSelection252']['source'];inputs[v['path']]=v;S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-merkle-sparse243-source02/generate.py').read_bytes());put('templates01.json',dict(modules={'CompilerPackedTruth257':dict(body=body,names=['row_selected','selected_sound']),'CapturedPackedCandidate257':dict(body=actual,names=['rows'])},inputs=inputs,scope=dict(status='SOURCE_ONLY_UNRUN',goal='Exact qualified pack checker transfers selected actual arithmetic/copy rows to independent candidate; no FullSAT/desired row/hash premise',open=['Kernel qualification','component instantiation','legal seed/all assertions/native'],runtime=c['runtime_sha'],source_context=c['canonical_context'])))
