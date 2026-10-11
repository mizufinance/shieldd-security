import ShielddSecurity.CapturedNextGlobal118
import ShielddSecurity.CapturedRegistryHighLimb121
import ShielddSecurity.HighBitMeaning122
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedHighLimbGlobal123
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
abbrev completed (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) : Nat → F :=
  CapturedNextGlobal118.completed
    (CapturedRegistryHighLimb121.seeded base (asset/2^128) (value/2^128))
    initial next asset value epoch position
theorem high_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position column : Nat) (lower : 981≤column) (upper : column<1110) :
    CapturedNextGlobal118.completed base initial next asset value epoch position column=base column := by
  have small : column<22738 := by omega
  have notVerifier : column≠1 ∧ column≠2 ∧ column≠copy := by
    have c : copy=200692 := rfl
    omega
  have notEpoch : ¬(49≤column ∧ column<135) := by omega
  have notPosition : 216≤column := by omega
  have seedSmall : ∀ c∈CapturedFourSubgroupSeed89.hintColumns,c<216 := by decide
  have notSeed : column∉CapturedFourSubgroupSeed89.hintColumns := by
    intro member
    have h:=seedSmall column member
    omega
  have a:=(CapturedGlobalPosition77.outside
    (CapturedFourSubgroupSeed89.seeded (CapturedRegistryValueRange97.completed
      (CapturedRegistryAssetRange109.completed (CapturedRegistryNextRange114.completed base next) asset) value) initial)
    epoch position column (Or.inl small) notVerifier notEpoch (Or.inr notPosition)).trans
      (CapturedFourSubgroupSeed89.seeded_outside _ initial _ notSeed)
  exact a.trans ((CapturedRegistryValueRange97.completed_outside _ value column (Or.inr (by omega))).trans
    ((CapturedRegistryAssetRange109.completed_outside _ asset column (Or.inr (by omega))).trans
      (CapturedRegistryNextRange114.completed_outside _ next column (Or.inr (by omega)))))
theorem inside (base other : Nat → F) (a b column : Nat) (lower : 981≤column) (upper : column<1110) :
    CapturedRegistryHighLimb121.seeded base a b column=CapturedRegistryHighLimb121.seeded other a b column := by
  by_cases bits : 983≤column
  · unfold CapturedRegistryHighLimb121.seeded writeBits
    have valid : 983≤column ∧ column<983+(encodeBits 127 (BoundedLimbComparison119.difference 127 a b)).length := by
      rw [encodeBits_length];omega
    simp only [if_pos valid]
  · have two : column=981 ∨ column=982 := by omega
    rcases two with rfl | rfl
    · rw [CapturedRegistryHighLimb121.borrow_value,CapturedRegistryHighLimb121.borrow_value]
    · rw [CapturedRegistryHighLimb121.difference_value,CapturedRegistryHighLimb121.difference_value]
theorem seeded_fixed (base rho : Nat → F) (a b : Nat)
    (frame : ∀ column,981≤column → column<1110 → rho column=CapturedRegistryHighLimb121.seeded base a b column) :
    CapturedRegistryHighLimb121.seeded rho a b=rho := by
  funext column
  by_cases lower : column<981
  · exact CapturedRegistryHighLimb121.outside rho a b column (Or.inl lower)
  · by_cases upper : 1110≤column
    · exact CapturedRegistryHighLimb121.outside rho a b column (Or.inr upper)
    · exact (inside rho base a b column (by omega) (by omega)).trans (frame column (by omega) (by omega)).symm
theorem final_seeded (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    CapturedRegistryHighLimb121.seeded (completed base initial next asset value epoch position)
      (asset/2^128) (value/2^128)=completed base initial next asset value epoch position := by
  apply seeded_fixed base
  intro column lower upper
  exact high_frame _ initial next asset value epoch position column lower upper
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
theorem asset_high (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (bound : asset<2^255) :
    fieldBinary (CapturedRegistryHighLimb120.leftColumns.map (completed base initial next asset value epoch position))=
      ((asset/2^128:Nat):F) :=
  HighBitMeaning122.high_meaning _ 471 asset bound (asset_bits base initial next asset value epoch position)
theorem value_high (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (bound : value<2^255) :
    fieldBinary (CapturedRegistryHighLimb120.rightColumns.map (completed base initial next asset value epoch position))=
      ((value/2^128:Nat):F) :=
  HighBitMeaning122.high_meaning _ 216 value bound (value_bits base initial next asset value epoch position)
theorem zero (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (one : base 0=1) :
    completed base initial next asset value epoch position 0=1 :=
  CapturedNextGlobal118.zero _ initial next asset value epoch position
    ((CapturedRegistryHighLimb121.outside base _ _ 0 (Or.inl (by decide))).trans one)
variable [CharP F p]
theorem arithmetic (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) :
    SatisfiesAt (completed base initial next asset value epoch position) CapturedFullArithmetic52.rowAt 177954 :=
  CapturedGlobalRegistered74.completed_arithmetic _ _
theorem high_assertions (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (next asset value epoch position : Nat) (left : asset<2^255) (right : value<2^255) :
    SatisfiesAt (completed base initial next asset value epoch position)
      (fun index => CapturedFullRelation58.rowAt (178893+index)) 130 := by
  have linked : completed base initial next asset value epoch position copy=completed base initial next asset value epoch position 0 :=
    CapturedGlobalRegistered74.completed_copy _ _
  have h:=CapturedRegistryHighLimb121.full_complete (completed base initial next asset value epoch position)
    (asset/2^128) (value/2^128) (HighBitMeaning122.high_bound asset left) (HighBitMeaning122.high_bound value right)
    (asset_high base initial next asset value epoch position left)
    (value_high base initial next asset value epoch position right) linked
  rw [final_seeded] at h
  exact h
end ShielddSecurity.CapturedHighLimbGlobal123
