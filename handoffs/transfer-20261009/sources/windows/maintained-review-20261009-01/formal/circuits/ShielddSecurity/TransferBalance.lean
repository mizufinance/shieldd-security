import ShielddSecurity.Arithmetic
import ShielddSecurity.TransferCore

set_option maxHeartbeats 300000

namespace ShielddSecurity.TransferBalance
open TransferCore

/-- Four 128-bit constituents and a 129-bit magnitude remain far below the
field modulus even after rearranging either signed branch. -/
theorem field_capacity : 4 * amountBound ≤ fieldModulus := by decide

/-- Arbitrary values satisfying the signed arithmetic equation have integer
meaning. Range/bit reconstruction, row membership and native group use remain
separate joins; no honest Rust witness is assumed here. -/
theorem signed_magnitude_sound {F : Type} [Field F] [CharP F fieldModulus]
    (in0 in1 out0 out1 magnitude : Nat) (negative : Bool)
    (in0Bound : in0 < amountBound) (in1Bound : in1 < amountBound)
    (out0Bound : out0 < amountBound) (out1Bound : out1 < amountBound)
    (magnitudeBound : magnitude < 2 * amountBound)
    (equation : (in0 : F) + (in1 : F) - (out0 : F) - (out1 : F) =
      if negative then -(magnitude : F) else (magnitude : F)) :
    (in0 : Int) + (in1 : Int) - (out0 : Int) - (out1 : Int) =
      if negative then -(magnitude : Int) else (magnitude : Int) := by
  have capacity := field_capacity
  cases negative with
  | false =>
    have rearranged : ((out0 + out1 + magnitude : Nat) : F) = ((in0 + in1 : Nat) : F) := by
      simp only [Bool.false_eq_true, ↓reduceIte] at equation
      simp only [Nat.cast_add]
      calc
        _ = ((in0 : F) + (in1 : F) - (out0 : F) - (out1 : F)) + (out0 : F) + (out1 : F) := by rw [equation]; ring
        _ = _ := by ring
    have integer := bounded_cast_injective (F := F) (p := fieldModulus)
      (a := out0 + out1 + magnitude) (b := in0 + in1) (by omega) (by omega) rearranged
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  | true =>
    have rearranged : ((in0 + in1 + magnitude : Nat) : F) = ((out0 + out1 : Nat) : F) := by
      simp only [↓reduceIte] at equation
      simp only [Nat.cast_add]
      calc
        _ = ((in0 : F) + (in1 : F) - (out0 : F) - (out1 : F)) + (magnitude : F) + (out0 : F) + (out1 : F) := by ring
        _ = _ := by rw [equation]; ring
    have integer := bounded_cast_injective (F := F) (p := fieldModulus)
      (a := in0 + in1 + magnitude) (b := out0 + out1) (by omega) (by omega) rearranged
    simp only [↓reduceIte]
    omega

/-- The negative-one representatives in the field and scalar group differ.
Encoding field negation as a positive scalar is not signed scalar conversion. -/
theorem negative_one_encodings_differ : fieldModulus - 1 ≠ scalarOrder - 1 := by decide

/-- Reducing a field-negative-one encoding as a positive scalar also gives the
wrong group scalar. This is an exact counterexample to that conversion, not
merely inequality between the unreduced representatives. -/
theorem field_negative_one_not_group_negative_one :
    (fieldModulus - 1) % scalarOrder ≠ scalarOrder - 1 := by decide

def effectiveScalar (negative : Bool) (magnitude : Nat) : Nat :=
  if negative then (scalarOrder - magnitude % scalarOrder) % scalarOrder
  else magnitude % scalarOrder

theorem effective_scalar_canonical (negative : Bool) (magnitude : Nat) :
    effectiveScalar negative magnitude < scalarOrder := by
  have positive : 0 < scalarOrder := by decide
  cases negative <;> exact Nat.mod_lt _ positive

theorem negative_zero_scalar : effectiveScalar true 0 = 0 := by decide
theorem negative_one_scalar : effectiveScalar true 1 = scalarOrder - 1 := by decide

set_option pp.all true in
#check @field_capacity
set_option pp.all true in
#check @signed_magnitude_sound
set_option pp.all true in
#check @negative_one_encodings_differ
set_option pp.all true in
#check @field_negative_one_not_group_negative_one
set_option pp.all true in
#check @effective_scalar_canonical
set_option pp.all true in
#check @negative_zero_scalar
set_option pp.all true in
#check @negative_one_scalar
#print axioms field_capacity
#print axioms signed_magnitude_sound
#print axioms negative_one_encodings_differ
#print axioms field_negative_one_not_group_negative_one
#print axioms effective_scalar_canonical
#print axioms negative_zero_scalar
#print axioms negative_one_scalar

end ShielddSecurity.TransferBalance
