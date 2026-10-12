import ShielddSecurity.CapturedCall04GlobalBinding168E02
import ShielddSecurity.CapturedArithmeticSelection252
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateRows258P008
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) CapturedCall04GlobalBinding168E02.rows := by
 apply CapturedArithmeticSelection252.candidate_rows base CapturedCall04GlobalBinding168E02.indices CapturedCall04GlobalBinding168E02.rows CapturedCall04GlobalBinding168E02.checked
 change ∀ index∈List.range' 514 16,CapturedArithmeticSelection252.Supported index
 exact CapturedArithmeticSelection252.range_supported 514 16 (by omega)
end ShielddSecurity.CandidateRows258P008

set_option pp.all true in
#check @ShielddSecurity.CandidateRows258P008.rows
#print axioms ShielddSecurity.CandidateRows258P008.rows
