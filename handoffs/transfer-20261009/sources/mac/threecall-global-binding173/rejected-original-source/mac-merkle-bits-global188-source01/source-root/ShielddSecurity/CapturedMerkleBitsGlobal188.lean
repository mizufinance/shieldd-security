import ShielddSecurity.MerkleBits29
import ShielddSecurity.BooleanDecode150
import ShielddSecurity.CompilerIndexedCopyStream171
import ShielddSecurity.CapturedFullRelation58
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleBitsGlobal188
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770
 MerkleBits29.captureIndices MerkleBits29.actualRows
theorem checked : productionCheck=true := by decide +kernel
def booleanCheck : Bool := MerkleBits29.columns.all (fun i => decide (booleanRow i∈MerkleBits29.referenceRows))
theorem boolean_checked : booleanCheck=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem rows_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho MerkleBits29.actualRows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 MerkleBits29.captureIndices
 MerkleBits29.actualRows checked rho ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
theorem position (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^32 ∧ (n:F)=rho 135 := MerkleBits29.position_bound rho (rows_sound rho satisfied)
theorem canonical_position (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (n : Nat) (canonical : n<p) (meaning : (n:F)=rho 135) : n<2^32 := by
 obtain ⟨m,bound,equal⟩ := position rho satisfied
 have small : m<p := lt_trans bound (by decide : 2^32<p)
 have same := CapturedEpochHints62.cast_small_unique m n small canonical (equal.trans meaning.symm)
 simpa only [same] using bound
theorem bit_fields (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (n : Nat) (canonical : n<p) (meaning : (n:F)=rho 135) :
 MerkleBits29.columns.map rho=(encodeBits 32 n).map (fun bit => if bit then (1:F) else 0) := by
 have reference := MerkleBits29.reference_satisfied rho (rows_sound rho satisfied)
 have boolean := rows_bits_sound MerkleBits29.referenceRows MerkleBits29.columns boolean_checked rho reference
 have reconstruction : reconstructionRow 135 MerkleBits29.columns∈MerkleBits29.referenceRows :=
   List.mem_append_right _ (by simp [MerkleBits29.referenceRows])
 have value := reconstruction_row_sound MerkleBits29.referenceRows 135 MerkleBits29.columns reconstruction rho reference
 have length : (MerkleBits29.columns.map rho).length=32 := by
   simp only [List.length_map,MerkleBits29.counts.2.2.2]
 have finite : 2^(MerkleBits29.columns.map rho).length<p := by rw [length];decide
 simpa only [length] using BooleanDecode150.canonical_bits (MerkleBits29.columns.map rho) n finite canonical boolean (value.trans meaning.symm)
end ShielddSecurity.CapturedMerkleBitsGlobal188

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleBitsGlobal188.productionCheck
#print axioms ShielddSecurity.CapturedMerkleBitsGlobal188.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleBitsGlobal188.checked
#print axioms ShielddSecurity.CapturedMerkleBitsGlobal188.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleBitsGlobal188.booleanCheck
#print axioms ShielddSecurity.CapturedMerkleBitsGlobal188.booleanCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleBitsGlobal188.boolean_checked
#print axioms ShielddSecurity.CapturedMerkleBitsGlobal188.boolean_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleBitsGlobal188.rows_sound
#print axioms ShielddSecurity.CapturedMerkleBitsGlobal188.rows_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleBitsGlobal188.position
#print axioms ShielddSecurity.CapturedMerkleBitsGlobal188.position
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleBitsGlobal188.canonical_position
#print axioms ShielddSecurity.CapturedMerkleBitsGlobal188.canonical_position
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleBitsGlobal188.bit_fields
#print axioms ShielddSecurity.CapturedMerkleBitsGlobal188.bit_fields
