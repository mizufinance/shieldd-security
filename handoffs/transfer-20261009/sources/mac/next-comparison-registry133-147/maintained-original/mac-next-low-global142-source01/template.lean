import ShielddSecurity.CapturedNextHighZeroShared139
import ShielddSecurity.CapturedNextLowLimb141
import ShielddSecurity.LowBitMeaning128
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedNextLowGlobal142
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
abbrev completed (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) : Nat → F :=
  CapturedNextHighZeroShared139.completed
    (CapturedNextLowLimb141.seeded base (LowBitMeaning128.low next) (LowBitMeaning128.low asset))
    initial next asset value epoch position
theorem low_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position column : Nat) (lower : 1373≤column) (upper : column<1503) :
    CapturedNextHighZeroShared139.completed base initial next asset value epoch position column=base column := by
  exact (CapturedNextHighZeroShared139.early_frame _ initial next asset value epoch position column (by omega) (by omega)).trans
    ((CapturedNextHighLimb134.outside _ (next/2^128) (asset/2^128) column (Or.inr (by omega))).trans
      (FieldZeroSeed125.outside base 1371 (CapturedNextHighZeroShared139.difference next asset) column (Or.inr lower)))
theorem inside (base other : Nat → F) (a b column : Nat) (lower : 1373≤column) (upper : column<1503) :
    CapturedNextLowLimb141.seeded base a b column=CapturedNextLowLimb141.seeded other a b column := by
  by_cases bits : 1375≤column
  · unfold CapturedNextLowLimb141.seeded writeBits
    have valid : 1375≤column ∧ column<1375+(encodeBits 128 (BoundedLimbComparison119.difference 128 a b)).length := by
      rw [encodeBits_length];omega
    simp only [if_pos valid]
  · have two : column=1373 ∨ column=1374 := by omega
    rcases two with rfl | rfl
    · rw [CapturedNextLowLimb141.borrow_value,CapturedNextLowLimb141.borrow_value]
    · rw [CapturedNextLowLimb141.difference_value,CapturedNextLowLimb141.difference_value]
theorem seeded_fixed (base rho : Nat → F) (a b : Nat)
    (frame : ∀ column,1373≤column → column<1503 → rho column=CapturedNextLowLimb141.seeded base a b column) :
    CapturedNextLowLimb141.seeded rho a b=rho := by
  funext column
  by_cases lower : column<1373
  · exact CapturedNextLowLimb141.outside rho a b column (Or.inl lower)
  · by_cases upper : 1503≤column
    · exact CapturedNextLowLimb141.outside rho a b column (Or.inr upper)
    · exact (inside rho base a b column (by omega) (by omega)).trans (frame column (by omega) (by omega)).symm
theorem final_seeded (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    CapturedNextLowLimb141.seeded (completed base initial next asset value epoch position)
      (LowBitMeaning128.low next) (LowBitMeaning128.low asset)=completed base initial next asset value epoch position := by
  apply seeded_fixed base
  intro column lower upper
  exact low_frame _ initial next asset value epoch position column lower upper
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
theorem next_low (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    fieldBinary (CapturedNextLowLimb140.leftColumns.map (completed base initial next asset value epoch position))=
      (LowBitMeaning128.low next:F) :=
  LowBitMeaning128.low_meaning _ 726 next (next_bits base initial next asset value epoch position)
theorem asset_low (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    fieldBinary (CapturedNextLowLimb140.rightColumns.map (completed base initial next asset value epoch position))=
      (LowBitMeaning128.low asset:F) :=
  LowBitMeaning128.low_meaning _ 471 asset (asset_bits base initial next asset value epoch position)
theorem zero (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (one : base 0=1) :
    completed base initial next asset value epoch position 0=1 :=
  CapturedNextHighGlobal135.zero _ initial next asset value epoch position
    ((FieldZeroSeed125.outside _ _ _ 0 (Or.inl (by decide))).trans
      ((CapturedNextLowLimb141.outside base _ _ 0 (Or.inl (by decide))).trans one))
variable [CharP F p]
theorem arithmetic (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    SatisfiesAt (completed base initial next asset value epoch position) CapturedFullArithmetic52.rowAt 177954 :=
  CapturedGlobalRegistered74.completed_arithmetic _ _
theorem low_assertions (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    SatisfiesAt (completed base initial next asset value epoch position)
      (fun index => CapturedFullRelation58.rowAt (179290+index)) 131 := by
  have linked : completed base initial next asset value epoch position copy=completed base initial next asset value epoch position 0 :=
    CapturedGlobalRegistered74.completed_copy _ _
  have h:=CapturedNextLowLimb141.full_complete (completed base initial next asset value epoch position)
    (LowBitMeaning128.low next) (LowBitMeaning128.low asset) (LowBitMeaning128.low_bound next) (LowBitMeaning128.low_bound asset)
    (next_low base initial next asset value epoch position)
    (asset_low base initial next asset value epoch position) linked
  rw [final_seeded] at h
  exact h
end ShielddSecurity.CapturedNextLowGlobal142
