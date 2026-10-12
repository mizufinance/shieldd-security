import ShielddSecurity.CapturedCall04GlobalBinding168B01
import ShielddSecurity.CapturedIndexedCandidate260
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateRows258P002
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) CapturedCall04GlobalBinding168B01.rows := by
 apply CapturedIndexedCandidate260.rows base CapturedCall04GlobalBinding168B01.indices CapturedCall04GlobalBinding168B01.rows CapturedCall04GlobalBinding168B01.checked
 change ∀ index∈List.range' 386 32,CapturedArithmeticSelection252.Supported index
 exact CapturedArithmeticSelection252.range_supported 386 32 (by omega)
end ShielddSecurity.CandidateRows258P002

set_option pp.all true in
#check @ShielddSecurity.CandidateRows258P002.rows
#print axioms ShielddSecurity.CandidateRows258P002.rows
