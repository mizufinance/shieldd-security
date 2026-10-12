import ShielddSecurity.CompilerPackedTruth257
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

set_option pp.all true in
#check @ShielddSecurity.CapturedPackedCandidate257.rows
#print axioms ShielddSecurity.CapturedPackedCandidate257.rows
