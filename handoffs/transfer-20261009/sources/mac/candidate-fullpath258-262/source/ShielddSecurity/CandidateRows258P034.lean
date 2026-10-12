import ShielddSecurity.CapturedPriorGlobalBinding170G003
import ShielddSecurity.CapturedPackedCandidate257
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateRows258P034
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) CapturedPriorGlobalBinding170G003.rows := by
 apply CapturedPackedCandidate257.rows base CapturedPriorGlobalBinding170G003.indices CapturedPriorGlobalBinding170G003.rows CapturedPriorGlobalBinding170G003.checked
 change ∀ index∈List.range' 256 64,CapturedArithmeticSelection252.Supported index
 exact CapturedArithmeticSelection252.range_supported 256 64 (by omega)
end ShielddSecurity.CandidateRows258P034

set_option pp.all true in
#check @ShielddSecurity.CandidateRows258P034.rows
#print axioms ShielddSecurity.CandidateRows258P034.rows
