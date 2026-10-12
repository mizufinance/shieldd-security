import ShielddSecurity.CapturedCall04GlobalBinding167Pilot
import ShielddSecurity.CapturedIndexedCandidate260
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateRows258P000
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) CapturedCall04GlobalBinding167Pilot.rows := by
 apply CapturedIndexedCandidate260.rows base CapturedCall04GlobalBinding167Pilot.indices CapturedCall04GlobalBinding167Pilot.rows CapturedCall04GlobalBinding167Pilot.checked
 change ∀ index∈List.range' 322 32,CapturedArithmeticSelection252.Supported index
 exact CapturedArithmeticSelection252.range_supported 322 32 (by omega)
end ShielddSecurity.CandidateRows258P000

set_option pp.all true in
#check @ShielddSecurity.CandidateRows258P000.rows
#print axioms ShielddSecurity.CandidateRows258P000.rows
