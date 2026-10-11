import ShielddSecurity.CapturedLowLimbShared132
import ShielddSecurity.CapturedNextHighLimb134
import ShielddSecurity.HighBitMeaning122
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedNextHighGlobal135
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
abbrev completed (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) : Nat → F :=
  CapturedLowLimbShared132.completed
    (CapturedNextHighLimb134.seeded base (next/2^128) (asset/2^128))
    initial next asset value epoch position
theorem high_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position column : Nat) (lower : 1242≤column) (upper : column<1371) :
    CapturedLowLimbShared132.completed base initial next asset value epoch position column=base column := by
  exact (CapturedHighZeroShared127.early_frame _ initial next asset value epoch position column (by omega) (by omega)).trans
    ((CapturedRegistryHighLimb121.outside _ (asset/2^128) (value/2^128) column (Or.inr (by omega))).trans
      ((FieldZeroSeed125.outside _ 1110 (CapturedHighZeroShared127.difference asset value) column (Or.inr (by omega))).trans
        (CapturedRegistryLowLimb130.outside base (LowBitMeaning128.low asset) (LowBitMeaning128.low value) column (Or.inr lower))))
theorem inside (base other : Nat → F) (a b column : Nat) (lower : 1242≤column) (upper : column<1371) :
    CapturedNextHighLimb134.seeded base a b column=CapturedNextHighLimb134.seeded other a b column := by
  by_cases bits : 1244≤column
  · unfold CapturedNextHighLimb134.seeded writeBits
    have valid : 1244≤column ∧ column<1244+(encodeBits 127 (BoundedLimbComparison119.difference 127 a b)).length := by
      rw [encodeBits_length];omega
    simp only [if_pos valid]
  · have two : column=1242 ∨ column=1243 := by omega
    rcases two with rfl | rfl
    · rw [CapturedNextHighLimb134.borrow_value,CapturedNextHighLimb134.borrow_value]
    · rw [CapturedNextHighLimb134.difference_value,CapturedNextHighLimb134.difference_value]
theorem seeded_fixed (base rho : Nat → F) (a b : Nat)
    (frame : ∀ column,1242≤column → column<1371 → rho column=CapturedNextHighLimb134.seeded base a b column) :
    CapturedNextHighLimb134.seeded rho a b=rho := by
  funext column
  by_cases lower : column<1242
  · exact CapturedNextHighLimb134.outside rho a b column (Or.inl lower)
  · by_cases upper : 1371≤column
    · exact CapturedNextHighLimb134.outside rho a b column (Or.inr upper)
    · exact (inside rho base a b column (by omega) (by omega)).trans (frame column (by omega) (by omega)).symm
theorem final_seeded (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    CapturedNextHighLimb134.seeded (completed base initial next asset value epoch position)
      (next/2^128) (asset/2^128)=completed base initial next asset value epoch position := by
  apply seeded_fixed base
  intro column lower upper
  exact high_frame _ initial next asset value epoch position column lower upper
theorem next_bits (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position index : Nat) (bound : index<255) :
    completed base initial next asset value epoch position (726+index)=
      if (encodeBits 255 next)[index]?.getD false then 1 else 0 := by
  exact (show _=BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt next (216+index)) from
    CapturedNextGlobal118.bits _ initial next asset value epoch position index bound).trans
      (by simp only [BinaryComparison100.bit,CapturedValueComparison106.bitAt,Nat.add_sub_cancel_left])
theorem asset_bits (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position index : Nat) (bound : index<255) :
    completed base initial next asset value epoch position (471+index)=
      if (encodeBits 255 asset)[index]?.getD false then 1 else 0 := by
  exact (show _=BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt asset (216+index)) from
    CapturedAssetGlobal113.bits _ initial asset value epoch position index bound).trans
      (by simp only [BinaryComparison100.bit,CapturedValueComparison106.bitAt,Nat.add_sub_cancel_left])
theorem next_high (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (bound : next<2^255) :
    fieldBinary (CapturedNextHighLimb133.leftColumns.map (completed base initial next asset value epoch position))=
      ((next/2^128:Nat):F) :=
  HighBitMeaning122.high_meaning _ 726 next bound (next_bits base initial next asset value epoch position)
theorem asset_high (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (bound : asset<2^255) :
    fieldBinary (CapturedNextHighLimb133.rightColumns.map (completed base initial next asset value epoch position))=
      ((asset/2^128:Nat):F) :=
  HighBitMeaning122.high_meaning _ 471 asset bound (asset_bits base initial next asset value epoch position)
theorem zero (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (one : base 0=1) :
    completed base initial next asset value epoch position 0=1 :=
  CapturedLowLimbGlobal131.zero _ initial next asset value epoch position
    ((CapturedNextHighLimb134.outside base _ _ 0 (Or.inl (by decide))).trans one)
variable [CharP F p]
theorem arithmetic (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    SatisfiesAt (completed base initial next asset value epoch position) CapturedFullArithmetic52.rowAt 177954 :=
  CapturedGlobalRegistered74.completed_arithmetic _ _
theorem high_assertions (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (left : next<2^255) (right : asset<2^255) :
    SatisfiesAt (completed base initial next asset value epoch position)
      (fun index => CapturedFullRelation58.rowAt (179157+index)) 130 := by
  have linked : completed base initial next asset value epoch position copy=completed base initial next asset value epoch position 0 :=
    CapturedGlobalRegistered74.completed_copy _ _
  have h:=CapturedNextHighLimb134.full_complete (completed base initial next asset value epoch position)
    (next/2^128) (asset/2^128) (HighBitMeaning122.high_bound next left) (HighBitMeaning122.high_bound asset right)
    (next_high base initial next asset value epoch position left)
    (asset_high base initial next asset value epoch position right) linked
  rw [final_seeded] at h
  exact h
end ShielddSecurity.CapturedNextHighGlobal135
