import ShielddSecurity.CapturedPriorPack179Pilot64
import ShielddSecurity.CapturedPackedCandidate257
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateRows258P030
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) CapturedPriorPack179Pilot64.rows := by
 apply CapturedPackedCandidate257.rows base CapturedPriorPack179Pilot64.indices CapturedPriorPack179Pilot64.rows CapturedPriorPack179Pilot64.checked
 change ∀ index∈List.range' 0 64,CapturedArithmeticSelection252.Supported index
 exact CapturedArithmeticSelection252.range_supported 0 64 (by omega)
end ShielddSecurity.CandidateRows258P030

set_option pp.all true in
#check @ShielddSecurity.CandidateRows258P030.rows
#print axioms ShielddSecurity.CandidateRows258P030.rows
