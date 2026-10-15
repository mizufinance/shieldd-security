import ShielddSecurity.TransferBlstArmInverseWordMultiplyValue01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordMultiplyOverflow01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseWordMultiplyCarry01 (sourceUnsignedWordMultiply)
open TransferBlstArmInverseWordMultiplyValue01 (original_shifted_partial_product_carry_chain_conserves_the_entire_unsigned_product)

/-! Extra-word capacity and overflow from separately qualified conservation;
compiled ISA/flags execution remains separate. -/

attribute [local irreducible] sourceUnsignedWordMultiply

theorem every_entire_unsigned_word_product_fits_the_derived_extra_word_capacity
    (words : List UInt64) (multiplier : UInt64) :
    packWords words * multiplier.toNat < radix64 ^ (words.length + 1) := by
  have packed := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power words
  have multiplierBound : multiplier.toNat < radix64 := multiplier.toNat_lt
  have positive : 0 < radix64 ^ words.length := Nat.pow_pos (by decide : 0 < radix64)
  have weak := Nat.mul_le_mul_right multiplier.toNat (Nat.le_of_lt packed)
  have strong := Nat.mul_lt_mul_of_pos_left multiplierBound positive
  rw [Nat.pow_succ]
  exact Nat.lt_of_le_of_lt weak strong

theorem an_exact_bounded_unsigned_carry_equation_forces_a_clear_flag_and_the_entire_value
    (output capacity product : Nat) (carry : Bool)
    (conserved : output + capacity * carry.toNat = product) (bounded : product < capacity) :
    carry = false ∧ output = product := by
  cases carry with
  | false =>
    change output + capacity * 0 = product at conserved
    refine ⟨rfl, ?_⟩
    omega
  | true =>
    change output + capacity * 1 = product at conserved
    omega

theorem original_entire_unsigned_word_product_has_no_final_overflow_and_the_exact_full_value
    (words : List UInt64) (multiplier : UInt64) :
    (sourceUnsignedWordMultiply words multiplier).2 = false ∧
      packWords (sourceUnsignedWordMultiply words multiplier).1 = packWords words * multiplier.toNat := by
  exact an_exact_bounded_unsigned_carry_equation_forces_a_clear_flag_and_the_entire_value
    (packWords (sourceUnsignedWordMultiply words multiplier).1) (radix64 ^ (words.length + 1))
    (packWords words * multiplier.toNat) (sourceUnsignedWordMultiply words multiplier).2
    (original_shifted_partial_product_carry_chain_conserves_the_entire_unsigned_product words multiplier)
    (every_entire_unsigned_word_product_fits_the_derived_extra_word_capacity words multiplier)

set_option pp.all true in
#check @every_entire_unsigned_word_product_fits_the_derived_extra_word_capacity
#print axioms every_entire_unsigned_word_product_fits_the_derived_extra_word_capacity
set_option pp.all true in
#check @an_exact_bounded_unsigned_carry_equation_forces_a_clear_flag_and_the_entire_value
#print axioms an_exact_bounded_unsigned_carry_equation_forces_a_clear_flag_and_the_entire_value
set_option pp.all true in
#check @original_entire_unsigned_word_product_has_no_final_overflow_and_the_exact_full_value
#print axioms original_entire_unsigned_word_product_has_no_final_overflow_and_the_exact_full_value
end ShielddSecurity.TransferBlstArmInverseWordMultiplyOverflow01
