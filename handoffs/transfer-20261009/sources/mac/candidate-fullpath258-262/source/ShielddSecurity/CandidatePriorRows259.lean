import ShielddSecurity.CandidateCall04Rows259
import ShielddSecurity.CapturedPriorGlobalBinding170
import ShielddSecurity.CompilerSelectedChunks172
import ShielddSecurity.CompilerCandidateAssembly259
import ShielddSecurity.CandidateRows258P030
import ShielddSecurity.CandidateRows258P031
import ShielddSecurity.CandidateRows258P032
import ShielddSecurity.CandidateRows258P033
import ShielddSecurity.CandidateRows258P034
import ShielddSecurity.CandidateRows258P035
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidatePriorRows259
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41 CompilerSelectedChunks172
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (CapturedPriorGlobalBinding170.headRows) := by
 rw [←CapturedPriorGlobalBinding170.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedPriorPack179Pilot64.rows,CapturedPriorGlobalBinding170G000.rows,CapturedPriorGlobalBinding170G001.rows,CapturedPriorGlobalBinding170G002.rows,CapturedPriorGlobalBinding170G003.rows,CapturedPriorGlobalBinding170G004.rows]
 exact ⟨CandidateRows258P030.rows base,⟨CandidateRows258P031.rows base,⟨CandidateRows258P032.rows base,⟨CandidateRows258P033.rows base,⟨CandidateRows258P034.rows base,⟨CandidateRows258P035.rows base,True.intro⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) CapturedPriorRows16Frame01.capturedPriorRows := by
 intro row member
 rw [←CapturedPriorGlobalBinding170.prior_partition] at member
 rcases List.mem_append.mp member with before|later
 · exact arithmetic base row before
 · exact CandidateCall04Rows259.arithmetic base row later
end ShielddSecurity.CandidatePriorRows259

set_option pp.all true in
#check @ShielddSecurity.CandidatePriorRows259.arithmetic
#print axioms ShielddSecurity.CandidatePriorRows259.arithmetic
set_option pp.all true in
#check @ShielddSecurity.CandidatePriorRows259.rows
#print axioms ShielddSecurity.CandidatePriorRows259.rows
