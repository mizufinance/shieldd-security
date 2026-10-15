import ShielddSecurity.TransferBlstArmInversePartialProductSplit01
import ShielddSecurity.TransferBlstArmInverseCapturedCarry01
import ShielddSecurity.TransferBlstArmInverseWordSum01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePartialRowBoundary01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInversePartialProductSplit01 (sourcePartialWordMultiply)
open TransferBlstArmInverseCapturedCarry01 (sourceCapturedProductCarryWord)
open TransferBlstArmInverseWordSum01 (sourceWordSum)
attribute [local irreducible] sourcePartialWordMultiply sourceCapturedProductCarryWord sourceWordSum

/-! The two source partial-product blocks and their low-row carry sum expose
the complete unsigned row value at the split boundary. The accumulated
carry word is produced by actual source captures. Signed operand layout,
high correction and compiled execution remain separate. -/

def sourcePartialRowBoundary (left right : List UInt64) (first second : UInt64) :
    List UInt64 × UInt64 × UInt64 × UInt64 :=
  let u := sourcePartialWordMultiply left first 0 false
  let v := sourcePartialWordMultiply right second 0 false
  let row := sourceWordSum u.1 v.1
  (row.1, u.2.2, v.2.2, sourceCapturedProductCarryWord u.2.1 v.2.1 row.2)

theorem both_source_partial_products_have_equal_width_whenever_their_inputs_do
    (left right : List UInt64) (first second : UInt64) (same : left.length = right.length) :
    (sourcePartialWordMultiply left first 0 false).1.length =
      (sourcePartialWordMultiply right second 0 false).1.length := by
  simp only [TransferBlstArmInversePartialProductSplit01.every_partial_word_product_retains_the_entire_input_word_count, same]

theorem the_source_partial_row_boundary_retains_the_entire_low_input_width
    (left right : List UInt64) (first second : UInt64) (same : left.length = right.length) :
    (sourcePartialRowBoundary left right first second).1.length = left.length := by
  unfold sourcePartialRowBoundary
  rw [TransferBlstArmInverseWordSum01.equal_width_source_word_addition_retains_the_entire_output_width _ _
    (both_source_partial_products_have_equal_width_whenever_their_inputs_do left right first second same),
    TransferBlstArmInversePartialProductSplit01.every_partial_word_product_retains_the_entire_input_word_count]

theorem both_partial_products_and_the_actual_captured_row_boundary_conserve_the_entire_unsigned_linear_combination
    (left right : List UInt64) (first second : UInt64) (same : left.length = right.length) :
    let output := sourcePartialRowBoundary left right first second
    packWords output.1 + radix64 ^ left.length *
        (output.2.1.toNat + output.2.2.1.toNat + output.2.2.2.toNat) =
      packWords left * first.toNat + packWords right * second.toNat := by
  let u := sourcePartialWordMultiply left first 0 false
  let v := sourcePartialWordMultiply right second 0 false
  let row := sourceWordSum u.1 v.1
  have leftProduct := TransferBlstArmInversePartialProductSplit01.every_partial_word_product_conserves_the_full_integer_with_both_captured_boundary_values left first 0 false
  have rightProduct := TransferBlstArmInversePartialProductSplit01.every_partial_word_product_conserves_the_full_integer_with_both_captured_boundary_values right second 0 false
  simp only [UInt64.toNat_zero, Bool.toNat_false, Nat.add_zero] at leftProduct rightProduct
  rw [← same] at rightProduct
  have rowAddition := TransferBlstArmInverseWordSum01.equal_width_source_word_addition_conserves_the_full_sum_and_final_carry
    u.1 v.1 (both_source_partial_products_have_equal_width_whenever_their_inputs_do left right first second same)
  rw [TransferBlstArmInversePartialProductSplit01.every_partial_word_product_retains_the_entire_input_word_count] at rowAddition
  have boundary := TransferBlstArmInverseCapturedCarry01.two_full_partial_products_and_the_low_row_sum_derive_the_entire_combined_high_boundary
    (radix64 ^ left.length) (packWords u.1) (packWords v.1) u.2.2.toNat v.2.2.toNat
    (packWords row.1) u.2.1 v.2.1 row.2 rowAddition
  rw [leftProduct, rightProduct] at boundary
  exact boundary.symm

theorem the_actual_captured_carry_word_at_every_source_partial_row_boundary_is_at_most_three
    (left right : List UInt64) (first second : UInt64) :
    (sourcePartialRowBoundary left right first second).2.2.2.toNat ≤ 3 := by
  unfold sourcePartialRowBoundary
  exact TransferBlstArmInverseCapturedCarry01.the_entire_accumulated_product_and_row_carry_word_is_at_most_three _ _ _

set_option pp.all true in
#check @sourcePartialRowBoundary
#print axioms sourcePartialRowBoundary
set_option pp.all true in
#check @both_source_partial_products_have_equal_width_whenever_their_inputs_do
#print axioms both_source_partial_products_have_equal_width_whenever_their_inputs_do
set_option pp.all true in
#check @the_source_partial_row_boundary_retains_the_entire_low_input_width
#print axioms the_source_partial_row_boundary_retains_the_entire_low_input_width
set_option pp.all true in
#check @both_partial_products_and_the_actual_captured_row_boundary_conserve_the_entire_unsigned_linear_combination
#print axioms both_partial_products_and_the_actual_captured_row_boundary_conserve_the_entire_unsigned_linear_combination
set_option pp.all true in
#check @the_actual_captured_carry_word_at_every_source_partial_row_boundary_is_at_most_three
#print axioms the_actual_captured_carry_word_at_every_source_partial_row_boundary_is_at_most_three
end ShielddSecurity.TransferBlstArmInversePartialRowBoundary01
