import ShielddSecurity.CapturedJoinPack179Pilot32
import ShielddSecurity.CapturedPackedCandidate257
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateRows258P036
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) CapturedJoinPack179Pilot32.rows := by
 apply CapturedPackedCandidate257.rows base CapturedJoinPack179Pilot32.indices CapturedJoinPack179Pilot32.rows CapturedJoinPack179Pilot32.checked
 change ∀ index∈List.range' 734 32,CapturedArithmeticSelection252.Supported index
 exact CapturedArithmeticSelection252.range_supported 734 32 (by omega)
end ShielddSecurity.CandidateRows258P036

set_option pp.all true in
#check @ShielddSecurity.CandidateRows258P036.rows
#print axioms ShielddSecurity.CandidateRows258P036.rows
