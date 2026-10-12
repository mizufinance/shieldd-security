from pathlib import Path
import sys,json,hashlib,runpy
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution277';S=W/'mac-collection-candidate256-source01'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated');require(not S.exists(),'immutable');g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_ONLY');c=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);q=json.loads(Path(c['closure']['path']).read_bytes())['modules'];q.update(c['qualified_batch_imports']);inputs={}
for n in ['CompilerIndexedCopyCollection174','CompilerIndexedCopyStream171']:
 v=q[n]['source'];require(pin(Path(v['path']))==v,'exact accepted source');inputs[v['path']]=v
v=c['modules']['CapturedArithmeticSelection252']['source'];inputs[v['path']]=v
body='''import ShielddSecurity.CompilerIndexedCopyCollection174
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerCollectionStream256
open Compiler CompilerAssertionBlock51
theorem row_weaken (p copy : Nat) (parent : Nat → Option Row) (length position : Nat) (target : Row)
 (checked : CompilerIndexedCopyCollection174.rowCheck copy parent length position target=true) :
 CompilerIndexedCopyStream171.rowCheck p copy parent length position target=true := by
 cases found:parent position with
 | none => simp only [CompilerIndexedCopyCollection174.rowCheck,found] at checked;contradiction
 | some actual =>
   simp only [CompilerIndexedCopyCollection174.rowCheck,found] at checked
   have facts : position<length ∧collect (unoutline copy actual.a)=collect (unoutline copy target.a) ∧
     collect (unoutline copy actual.b)=collect (unoutline copy target.b) := of_decide_eq_true checked
   simp only [CompilerIndexedCopyStream171.rowCheck,found]
   apply decide_eq_true
   exact ⟨facts.1,congrArg (reduceCoefficients p) facts.2.1,congrArg (reduceCoefficients p) facts.2.2⟩
theorem check_weaken (p copy : Nat) (parent : Nat → Option Row) (length : Nat)
 (indices : List Nat) (targets : List Row)
 (checked : CompilerIndexedCopyCollection174.check copy parent length indices targets=true) :
 CompilerIndexedCopyStream171.check p copy parent length indices targets=true := by
 induction indices generalizing targets with
 | nil =>
   cases targets with
   | nil => rfl
   | cons a rest => simp only [CompilerIndexedCopyCollection174.check] at checked;contradiction
 | cons position indices ih =>
   cases targets with
   | nil => simp only [CompilerIndexedCopyCollection174.check] at checked;contradiction
   | cons target rest =>
     have facts:=Bool.and_eq_true_iff.mp checked
     exact Bool.and_eq_true_iff.mpr ⟨row_weaken p copy parent length position target facts.1,ih rest facts.2⟩
end ShielddSecurity.CompilerCollectionStream256
'''
actual='''import ShielddSecurity.CompilerCollectionStream256
import ShielddSecurity.CapturedArithmeticSelection252
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedCollectionCandidate256
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) (indices : List Nat) (targets : List Row)
 (checked : CompilerIndexedCopyCollection174.check copy CapturedFullRelation58.rowAt 200770 indices targets=true)
 (supports : ∀ index∈indices,CapturedArithmeticSelection252.Supported index) :
 Satisfies (CapturedFullRelation58.candidate base) targets :=
 CapturedArithmeticSelection252.candidate_rows base indices targets
   (CompilerCollectionStream256.check_weaken p copy _ _ indices targets checked) supports
end ShielddSecurity.CapturedCollectionCandidate256
'''
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-merkle-sparse243-source02/generate.py').read_bytes());put('templates01.json',dict(modules={'CompilerCollectionStream256':dict(body=body,names=['row_weaken','check_weaken']),'CapturedCollectionCandidate256':dict(body=actual,names=['rows'])},inputs=inputs,scope=dict(status='SOURCE_ONLY_UNRUN',goal='Reuse exact collect/unoutline certificates for prior/Join/registry candidate without asserting target truths or full relation',open=['Kernel qualification','legal seed/assertions/native'],runtime=c['runtime_sha'],source_context=c['canonical_context'])))
