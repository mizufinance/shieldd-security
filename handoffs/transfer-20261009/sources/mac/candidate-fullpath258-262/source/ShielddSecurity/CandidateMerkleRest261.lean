import ShielddSecurity.MerkleCandidateLevel255L00
import ShielddSecurity.MerkleCandidateLevel255L01
import ShielddSecurity.MerkleCandidateLevel255L02
import ShielddSecurity.MerkleCandidateLevel255L03
import ShielddSecurity.MerkleCandidateLevel255L04
import ShielddSecurity.MerkleCandidateLevel255L05
import ShielddSecurity.MerkleCandidateLevel255L06
import ShielddSecurity.MerkleCandidateLevel255L07
import ShielddSecurity.MerkleCandidateLevel255L08
import ShielddSecurity.MerkleCandidateLevel255L09
import ShielddSecurity.MerkleCandidateLevel255L10
import ShielddSecurity.MerkleCandidateLevel255L11
import ShielddSecurity.MerkleCandidateLevel255L12
import ShielddSecurity.MerkleCandidateLevel255L13
import ShielddSecurity.MerkleCandidateLevel255L14
import ShielddSecurity.MerklePath33Meaning
import ShielddSecurity.CompilerIndexedSlices183
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateMerkleRest261
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem level_rows (base : Nat → F) (i : Fin 15) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) i) := by
 have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by
   have bound:=i.isLt
   simp only [Fin.ext_iff]
   omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact MerkleCandidateLevel255L00.rows base
 · exact MerkleCandidateLevel255L01.rows base
 · exact MerkleCandidateLevel255L02.rows base
 · exact MerkleCandidateLevel255L03.rows base
 · exact MerkleCandidateLevel255L04.rows base
 · exact MerkleCandidateLevel255L05.rows base
 · exact MerkleCandidateLevel255L06.rows base
 · exact MerkleCandidateLevel255L07.rows base
 · exact MerkleCandidateLevel255L08.rows base
 · exact MerkleCandidateLevel255L09.rows base
 · exact MerkleCandidateLevel255L10.rows base
 · exact MerkleCandidateLevel255L11.rows base
 · exact MerkleCandidateLevel255L12.rows base
 · exact MerkleCandidateLevel255L13.rows base
 · exact MerkleCandidateLevel255L14.rows base
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerklePath33.rows (F:=F)) := by
 change Satisfies (CapturedFullRelation58.candidate base) (CompilerSegmentChain33.rows copy (MerklePath33.piece (F:=F)) 15)
 apply CompilerIndexedSlices183.chain_sound
 intro i less
 change Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) ⟨i%15,Nat.mod_lt i (by decide)⟩)
 exact level_rows base _
end ShielddSecurity.CandidateMerkleRest261

set_option pp.all true in
#check @ShielddSecurity.CandidateMerkleRest261.level_rows
#print axioms ShielddSecurity.CandidateMerkleRest261.level_rows
set_option pp.all true in
#check @ShielddSecurity.CandidateMerkleRest261.rows
#print axioms ShielddSecurity.CandidateMerkleRest261.rows
