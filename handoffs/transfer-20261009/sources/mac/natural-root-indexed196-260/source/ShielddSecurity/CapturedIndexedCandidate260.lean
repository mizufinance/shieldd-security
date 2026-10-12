import ShielddSecurity.CompilerIndexedTruth260
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

set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedCandidate260.rows
#print axioms ShielddSecurity.CapturedIndexedCandidate260.rows
