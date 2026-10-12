import ShielddSecurity.CapturedMerkleFirstGlobal186
import ShielddSecurity.CompilerSelectedChunks172
import ShielddSecurity.CompilerCandidateAssembly259
import ShielddSecurity.CandidateBatch262B10
import ShielddSecurity.CandidateBatch262B11
import ShielddSecurity.CandidateBatch262B12
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateFirstMerkleRows259
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41 CompilerSelectedChunks172
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleHash27Whole.selectedRows.take 412) := by
 rw [←CapturedMerkleFirstGlobal186.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [CapturedMerkleFirstGlobal186B00.rows,CapturedMerkleFirstGlobal186B01.rows,CapturedMerkleFirstGlobal186B02.rows,CapturedMerkleFirstGlobal186B03.rows,CapturedMerkleFirstGlobal186B04.rows,CapturedMerkleFirstGlobal186B05.rows,CapturedMerkleFirstGlobal186B06.rows,CapturedMerkleFirstGlobal186B07.rows,CapturedMerkleFirstGlobal186B08.rows,CapturedMerkleFirstGlobal186B09.rows,CapturedMerkleFirstGlobal186B10.rows,CapturedMerkleFirstGlobal186B11.rows,CapturedMerkleFirstGlobal186B12.rows,CapturedMerkleFirstGlobal186B13.rows,CapturedMerkleFirstGlobal186B14.rows,CapturedMerkleFirstGlobal186B15.rows,CapturedMerkleFirstGlobal186B16.rows,CapturedMerkleFirstGlobal186B17.rows,CapturedMerkleFirstGlobal186B18.rows,CapturedMerkleFirstGlobal186B19.rows,CapturedMerkleFirstGlobal186B20.rows,CapturedMerkleFirstGlobal186B21.rows,CapturedMerkleFirstGlobal186B22.rows,CapturedMerkleFirstGlobal186B23.rows,CapturedMerkleFirstGlobal186B24.rows,CapturedMerkleFirstGlobal186B25.rows]
 exact ⟨CandidateRows258P206.rows base,⟨CandidateRows258P207.rows base,⟨CandidateRows258P208.rows base,⟨CandidateRows258P209.rows base,⟨CandidateRows258P210.rows base,⟨CandidateRows258P211.rows base,⟨CandidateRows258P212.rows base,⟨CandidateRows258P213.rows base,⟨CandidateRows258P214.rows base,⟨CandidateRows258P215.rows base,⟨CandidateRows258P216.rows base,⟨CandidateRows258P217.rows base,⟨CandidateRows258P218.rows base,⟨CandidateRows258P219.rows base,⟨CandidateRows258P220.rows base,⟨CandidateRows258P221.rows base,⟨CandidateRows258P222.rows base,⟨CandidateRows258P223.rows base,⟨CandidateRows258P224.rows base,⟨CandidateRows258P225.rows base,⟨CandidateRows258P226.rows base,⟨CandidateRows258P227.rows base,⟨CandidateRows258P228.rows base,⟨CandidateRows258P229.rows base,⟨CandidateRows258P230.rows base,⟨CandidateRows258P231.rows base,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) MerkleHash27Whole.selectedRows := by
 have copying : Satisfies (CapturedFullRelation58.candidate base) (MerkleHash27Whole.selectedRows.drop 412) :=
   CapturedArithmeticSelection252.candidate_rows base [200769] _ CapturedMerkleFirstGlobal186.copy_checked
     (CapturedArithmeticSelection252.copies_supported 1)
 intro row member
 rw [←List.take_append_drop 412 MerkleHash27Whole.selectedRows] at member
 rcases List.mem_append.mp member with before|later
 · exact arithmetic base row before
 · exact copying row later
end ShielddSecurity.CandidateFirstMerkleRows259

set_option pp.all true in
#check @ShielddSecurity.CandidateFirstMerkleRows259.arithmetic
#print axioms ShielddSecurity.CandidateFirstMerkleRows259.arithmetic
set_option pp.all true in
#check @ShielddSecurity.CandidateFirstMerkleRows259.rows
#print axioms ShielddSecurity.CandidateFirstMerkleRows259.rows
