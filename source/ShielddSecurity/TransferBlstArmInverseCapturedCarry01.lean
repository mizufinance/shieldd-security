import ShielddSecurity.TransferBlstArmInverseWordMultiplyOverflow01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseCapturedCarry01
open TransferScalarSerializationRange01 (radix64)
open TransferBlstArmCarryChains01 (sourceAddCarry)
attribute [local irreducible] sourceAddCarry

/-! The coefficient routine accumulates two product carry flags and the
low-row addition flag into a word. The result can be two or three, so it
must not be interpreted as a single Bool. These are source ADC arithmetic
and symbolic boundary equations; compiled flag provenance remains open. -/

def sourceCaptureCarryWord (word : UInt64) (carry : Bool) : UInt64 :=
  (sourceAddCarry word 0 carry).1

theorem every_bounded_source_adc_capture_has_the_entire_word_plus_actual_flag_value
    (word : UInt64) (carry : Bool) (bounded : word.toNat + carry.toNat < radix64) :
    (sourceCaptureCarryWord word carry).toNat = word.toNat + carry.toNat := by
  have conserved := TransferBlstArmCarryChains01.actual_add_carry_arithmetic_conserves_the_full_integer word 0 carry
  simp only [UInt64.toNat_zero, Nat.add_zero] at conserved
  have result := TransferBlstArmInverseWordMultiplyOverflow01.an_exact_bounded_unsigned_carry_equation_forces_a_clear_flag_and_the_entire_value
    _ _ _ _ conserved bounded
  exact result.2

attribute [local irreducible] sourceCaptureCarryWord

def sourceCapturedProductCarryWord (first second row : Bool) : UInt64 :=
  sourceCaptureCarryWord (sourceCaptureCarryWord (sourceCaptureCarryWord 0 first) second) row

theorem the_three_original_carry_captures_derive_the_entire_sum_of_their_actual_flags
    (first second row : Bool) :
    (sourceCapturedProductCarryWord first second row).toNat = first.toNat + second.toNat + row.toNat := by
  have firstBound : first.toNat ≤ 1 := by cases first <;> decide
  have secondBound : second.toNat ≤ 1 := by cases second <;> decide
  have rowBound : row.toNat ≤ 1 := by cases row <;> decide
  have firstValue := every_bounded_source_adc_capture_has_the_entire_word_plus_actual_flag_value 0 first
    (by change 0 + first.toNat < 18446744073709551616; omega)
  simp only [UInt64.toNat_zero, Nat.zero_add] at firstValue
  have secondValue := every_bounded_source_adc_capture_has_the_entire_word_plus_actual_flag_value (sourceCaptureCarryWord 0 first) second
    (by rw [firstValue]; change first.toNat + second.toNat < 18446744073709551616; omega)
  rw [firstValue] at secondValue
  have rowValue := every_bounded_source_adc_capture_has_the_entire_word_plus_actual_flag_value
    (sourceCaptureCarryWord (sourceCaptureCarryWord 0 first) second) row
    (by rw [secondValue]; change first.toNat + second.toNat + row.toNat < 18446744073709551616; omega)
  rw [secondValue] at rowValue
  exact rowValue

attribute [local irreducible] sourceCapturedProductCarryWord

theorem the_entire_accumulated_product_and_row_carry_word_is_at_most_three
    (first second row : Bool) : (sourceCapturedProductCarryWord first second row).toNat ≤ 3 := by
  rw [the_three_original_carry_captures_derive_the_entire_sum_of_their_actual_flags]
  cases first <;> cases second <;> cases row <;> decide

theorem two_full_partial_products_and_the_low_row_sum_derive_the_entire_combined_high_boundary
    (capacity lowFirst lowSecond highFirst highSecond lowRow : Nat) (first second row : Bool)
    (lowAddition : lowRow + capacity * row.toNat = lowFirst + lowSecond) :
    (lowFirst + capacity * (highFirst + first.toNat)) +
        (lowSecond + capacity * (highSecond + second.toNat)) =
      lowRow + capacity * (highFirst + highSecond + (sourceCapturedProductCarryWord first second row).toNat) := by
  rw [the_three_original_carry_captures_derive_the_entire_sum_of_their_actual_flags]
  calc
    _ = (lowFirst + lowSecond) + capacity * (highFirst + highSecond + first.toNat + second.toNat) := by ring1
    _ = (lowRow + capacity * row.toNat) + capacity * (highFirst + highSecond + first.toNat + second.toNat) := by rw [lowAddition]
    _ = _ := by ring1

set_option pp.all true in
#check @sourceCaptureCarryWord
#print axioms sourceCaptureCarryWord
set_option pp.all true in
#check @every_bounded_source_adc_capture_has_the_entire_word_plus_actual_flag_value
#print axioms every_bounded_source_adc_capture_has_the_entire_word_plus_actual_flag_value
set_option pp.all true in
#check @sourceCapturedProductCarryWord
#print axioms sourceCapturedProductCarryWord
set_option pp.all true in
#check @the_three_original_carry_captures_derive_the_entire_sum_of_their_actual_flags
#print axioms the_three_original_carry_captures_derive_the_entire_sum_of_their_actual_flags
set_option pp.all true in
#check @the_entire_accumulated_product_and_row_carry_word_is_at_most_three
#print axioms the_entire_accumulated_product_and_row_carry_word_is_at_most_three
set_option pp.all true in
#check @two_full_partial_products_and_the_low_row_sum_derive_the_entire_combined_high_boundary
#print axioms two_full_partial_products_and_the_low_row_sum_derive_the_entire_combined_high_boundary
end ShielddSecurity.TransferBlstArmInverseCapturedCarry01
