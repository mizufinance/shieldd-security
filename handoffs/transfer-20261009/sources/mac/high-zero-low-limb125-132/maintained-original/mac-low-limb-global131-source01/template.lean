import ShielddSecurity.CapturedHighZeroShared127
import ShielddSecurity.CapturedRegistryLowLimb130
import ShielddSecurity.LowBitMeaning128
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedLowLimbGlobal131
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
abbrev completed (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) : Nat → F :=
  CapturedHighZeroShared127.completed
    (CapturedRegistryLowLimb130.seeded base (LowBitMeaning128.low asset) (LowBitMeaning128.low value))
    initial next asset value epoch position
theorem low_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position column : Nat) (lower : 1112≤column) (upper : column<1242) :
    CapturedHighZeroShared127.completed base initial next asset value epoch position column=base column := by
  exact (CapturedHighZeroShared127.early_frame _ initial next asset value epoch position column (by omega) (by omega)).trans
    ((CapturedRegistryHighLimb121.outside _ (asset/2^128) (value/2^128) column (Or.inr (by omega))).trans
      (FieldZeroSeed125.outside base 1110 (CapturedHighZeroShared127.difference asset value) column (Or.inr lower)))
theorem inside (base other : Nat → F) (a b column : Nat) (lower : 1112≤column) (upper : column<1242) :
    CapturedRegistryLowLimb130.seeded base a b column=CapturedRegistryLowLimb130.seeded other a b column := by
  by_cases bits : 1114≤column
  · unfold CapturedRegistryLowLimb130.seeded writeBits
    have valid : 1114≤column ∧ column<1114+(encodeBits 128 (BoundedLimbComparison119.difference 128 a b)).length := by
      rw [encodeBits_length];omega
    simp only [if_pos valid]
  · have two : column=1112 ∨ column=1113 := by omega
    rcases two with rfl | rfl
    · rw [CapturedRegistryLowLimb130.borrow_value,CapturedRegistryLowLimb130.borrow_value]
    · rw [CapturedRegistryLowLimb130.difference_value,CapturedRegistryLowLimb130.difference_value]
theorem seeded_fixed (base rho : Nat → F) (a b : Nat)
    (frame : ∀ column,1112≤column → column<1242 → rho column=CapturedRegistryLowLimb130.seeded base a b column) :
    CapturedRegistryLowLimb130.seeded rho a b=rho := by
  funext column
  by_cases lower : column<1112
  · exact CapturedRegistryLowLimb130.outside rho a b column (Or.inl lower)
  · by_cases upper : 1242≤column
    · exact CapturedRegistryLowLimb130.outside rho a b column (Or.inr upper)
    · exact (inside rho base a b column (by omega) (by omega)).trans (frame column (by omega) (by omega)).symm
theorem final_seeded (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    CapturedRegistryLowLimb130.seeded (completed base initial next asset value epoch position)
      (LowBitMeaning128.low asset) (LowBitMeaning128.low value)=completed base initial next asset value epoch position := by
  apply seeded_fixed base
  intro column lower upper
  exact low_frame _ initial next asset value epoch position column lower upper
theorem asset_bits (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position index : Nat) (bound : index<255) :
    completed base initial next asset value epoch position (471+index)=
      if (encodeBits 255 asset)[index]?.getD false then 1 else 0 := by
  exact (show _=BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt asset (216+index)) from
    CapturedAssetGlobal113.bits _ initial asset value epoch position index bound).trans
      (by simp only [BinaryComparison100.bit,CapturedValueComparison106.bitAt,Nat.add_sub_cancel_left])
theorem value_bits (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position index : Nat) (bound : index<255) :
    completed base initial next asset value epoch position (216+index)=
      if (encodeBits 255 value)[index]?.getD false then 1 else 0 := by
  exact (show _=BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt value (216+index)) from
    CapturedValueGlobal108.bits _ initial value epoch position index bound).trans
      (by simp only [BinaryComparison100.bit,CapturedValueComparison106.bitAt,Nat.add_sub_cancel_left])
theorem asset_low (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    fieldBinary (CapturedRegistryLowLimb129.leftColumns.map (completed base initial next asset value epoch position))=
      (LowBitMeaning128.low asset:F) :=
  LowBitMeaning128.low_meaning _ 471 asset (asset_bits base initial next asset value epoch position)
theorem value_low (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    fieldBinary (CapturedRegistryLowLimb129.rightColumns.map (completed base initial next asset value epoch position))=
      (LowBitMeaning128.low value:F) :=
  LowBitMeaning128.low_meaning _ 216 value (value_bits base initial next asset value epoch position)
theorem zero (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (one : base 0=1) :
    completed base initial next asset value epoch position 0=1 :=
  CapturedHighLimbGlobal123.zero _ initial next asset value epoch position
    ((FieldZeroSeed125.outside _ _ _ 0 (Or.inl (by decide))).trans
      ((CapturedRegistryLowLimb130.outside base _ _ 0 (Or.inl (by decide))).trans one))
variable [CharP F p]
theorem arithmetic (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    SatisfiesAt (completed base initial next asset value epoch position) CapturedFullArithmetic52.rowAt 177954 :=
  CapturedGlobalRegistered74.completed_arithmetic _ _
theorem low_assertions (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    SatisfiesAt (completed base initial next asset value epoch position)
      (fun index => CapturedFullRelation58.rowAt (179026+index)) 131 := by
  have linked : completed base initial next asset value epoch position copy=completed base initial next asset value epoch position 0 :=
    CapturedGlobalRegistered74.completed_copy _ _
  have h:=CapturedRegistryLowLimb130.full_complete (completed base initial next asset value epoch position)
    (LowBitMeaning128.low asset) (LowBitMeaning128.low value) (LowBitMeaning128.low_bound asset) (LowBitMeaning128.low_bound value)
    (asset_low base initial next asset value epoch position)
    (value_low base initial next asset value epoch position) linked
  rw [final_seeded] at h
  exact h
end ShielddSecurity.CapturedLowLimbGlobal131
