import ShielddSecurity.CompilerCollectionStream256
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

set_option pp.all true in
#check @ShielddSecurity.CapturedCollectionCandidate256.rows
#print axioms ShielddSecurity.CapturedCollectionCandidate256.rows
