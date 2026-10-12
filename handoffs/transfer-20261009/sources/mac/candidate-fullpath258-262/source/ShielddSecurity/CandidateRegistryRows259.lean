import ShielddSecurity.CapturedRegistryGlobalBinding175
import ShielddSecurity.CompilerSelectedChunks172
import ShielddSecurity.CompilerCandidateAssembly259
import ShielddSecurity.CandidateBatch262B08
import ShielddSecurity.CandidateBatch262B09
import ShielddSecurity.CandidateBatch262B10
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateRegistryRows259
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41 CompilerSelectedChunks172
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (CapturedRegistryGlobalBinding175.arithmeticRows) := by
 rw [←CapturedRegistryGlobalBinding175.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedRegistryGlobalBinding175G00.rows,CapturedRegistryGlobalBinding175G01.rows,CapturedRegistryGlobalBinding175G02.rows,CapturedRegistryGlobalBinding175G03.rows,CapturedRegistryGlobalBinding175G04.rows,CapturedRegistryGlobalBinding175G05.rows,CapturedRegistryGlobalBinding175G06.rows,CapturedRegistryGlobalBinding175G07.rows,CapturedRegistryGlobalBinding175G08.rows,CapturedRegistryGlobalBinding175G09.rows,CapturedRegistryGlobalBinding175G10.rows,CapturedRegistryGlobalBinding175G11.rows,CapturedRegistryGlobalBinding175G12.rows,CapturedRegistryGlobalBinding175G13.rows,CapturedRegistryGlobalBinding175G14.rows,CapturedRegistryGlobalBinding175G15.rows,CapturedRegistryGlobalBinding175G16.rows,CapturedRegistryGlobalBinding175G17.rows,CapturedRegistryGlobalBinding175G18.rows,CapturedRegistryGlobalBinding175G19.rows,CapturedRegistryGlobalBinding175G20.rows,CapturedRegistryGlobalBinding175G21.rows,CapturedRegistryGlobalBinding175G22.rows,CapturedRegistryGlobalBinding175G23.rows,CapturedRegistryGlobalBinding175G24.rows,CapturedRegistryGlobalBinding175G25.rows]
 exact ⟨CandidateRows258P180.rows base,⟨CandidateRows258P181.rows base,⟨CandidateRows258P182.rows base,⟨CandidateRows258P183.rows base,⟨CandidateRows258P184.rows base,⟨CandidateRows258P185.rows base,⟨CandidateRows258P186.rows base,⟨CandidateRows258P187.rows base,⟨CandidateRows258P188.rows base,⟨CandidateRows258P189.rows base,⟨CandidateRows258P190.rows base,⟨CandidateRows258P191.rows base,⟨CandidateRows258P192.rows base,⟨CandidateRows258P193.rows base,⟨CandidateRows258P194.rows base,⟨CandidateRows258P195.rows base,⟨CandidateRows258P196.rows base,⟨CandidateRows258P197.rows base,⟨CandidateRows258P198.rows base,⟨CandidateRows258P199.rows base,⟨CandidateRows258P200.rows base,⟨CandidateRows258P201.rows base,⟨CandidateRows258P202.rows base,⟨CandidateRows258P203.rows base,⟨CandidateRows258P204.rows base,⟨CandidateRows258P205.rows base,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) RegistryWhole23.selectedRows := by
 have copying := CompilerCandidateAssembly259.copy_packed base TransferPoseidonCall04Shared01.rawCopy CapturedRegistryGlobalBinding175.copy_checked
 intro row member
 rw [←CapturedRegistryGlobalBinding175.selected_partition] at member
 rcases List.mem_append.mp member with before|later
 · exact arithmetic base row before
 · exact copying row later
end ShielddSecurity.CandidateRegistryRows259

set_option pp.all true in
#check @ShielddSecurity.CandidateRegistryRows259.arithmetic
#print axioms ShielddSecurity.CandidateRegistryRows259.arithmetic
set_option pp.all true in
#check @ShielddSecurity.CandidateRegistryRows259.rows
#print axioms ShielddSecurity.CandidateRegistryRows259.rows
