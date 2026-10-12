import ShielddSecurity.CapturedCall04GlobalBinding168F11
import ShielddSecurity.CapturedArithmeticSelection252
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateRows258P025
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) CapturedCall04GlobalBinding168F11.rows := by
 apply CapturedArithmeticSelection252.candidate_rows base CapturedCall04GlobalBinding168F11.indices CapturedCall04GlobalBinding168F11.rows CapturedCall04GlobalBinding168F11.checked
 change ∀ index∈List.range' 698 8,CapturedArithmeticSelection252.Supported index
 exact CapturedArithmeticSelection252.range_supported 698 8 (by omega)
end ShielddSecurity.CandidateRows258P025

set_option pp.all true in
#check @ShielddSecurity.CandidateRows258P025.rows
#print axioms ShielddSecurity.CandidateRows258P025.rows
