import ShielddSecurity.TransferBlstArmInverseWordSum01
import ShielddSecurity.TransferBlstArmInverseSignedProductDecode01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSignedProductSum01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseSignedWordMultiply01 (sourceSignedMagnitudeProductWords)
open TransferBlstArmInverseWordSum01 (sourceWordSum)
attribute [local irreducible] sourceSignedMagnitudeProductWords sourceWordSum

/-! The two actual source signed-product word lists feed the source carry
sum. Equal input widths and signed64 factor bounds remain explicit here;
the original factor-row bounds and compiled execution are separate links. -/

def sourceSignedProductSum (left right : List UInt64) (f g : Int) : List UInt64 × Bool :=
  sourceWordSum (sourceSignedMagnitudeProductWords left f).1
    (sourceSignedMagnitudeProductWords right g).1

theorem equal_input_widths_derive_the_full_extra_word_sum_width
    (left right : List UInt64) (f g : Int) (same : left.length = right.length) :
    (sourceSignedProductSum left right f g).1.length = left.length + 1 := by
  have first := TransferBlstArmInverseSignedWordMultiply01.every_source_signed_magnitude_product_retains_exactly_one_extra_word left f
  have second := TransferBlstArmInverseSignedWordMultiply01.every_source_signed_magnitude_product_retains_exactly_one_extra_word right g
  have equalProducts : (sourceSignedMagnitudeProductWords left f).1.length =
      (sourceSignedMagnitudeProductWords right g).1.length := by rw [first, second, same]
  have count := TransferBlstArmInverseWordSum01.equal_width_source_word_addition_retains_the_entire_output_width
    (sourceSignedMagnitudeProductWords left f).1 (sourceSignedMagnitudeProductWords right g).1 equalProducts
  rw [first] at count
  exact count

theorem original_two_signed_products_and_word_sum_derive_the_full_linear_combination_residue
    (left right : List UInt64) (f g : Int) (same : left.length = right.length)
    (fLower : -9223372036854775808 ≤ f) (fUpper : f < 9223372036854775808)
    (gLower : -9223372036854775808 ≤ g) (gUpper : g < 9223372036854775808)
    (leftNonzero : f < 0 → 0 < packWords left) (rightNonzero : g < 0 → 0 < packWords right) :
    (packWords (sourceSignedProductSum left right f g).1 : Int) % ((radix64 ^ (left.length + 1) : Nat) : Int) =
      ((packWords left : Int) * f + (packWords right : Int) * g) % ((radix64 ^ (left.length + 1) : Nat) : Int) := by
  have first := TransferBlstArmInverseSignedWordMultiply01.every_source_signed_magnitude_product_retains_exactly_one_extra_word left f
  have second := TransferBlstArmInverseSignedWordMultiply01.every_source_signed_magnitude_product_retains_exactly_one_extra_word right g
  have equalProducts : (sourceSignedMagnitudeProductWords left f).1.length =
      (sourceSignedMagnitudeProductWords right g).1.length := by rw [first, second, same]
  have added := TransferBlstArmInverseWordSum01.equal_width_source_word_addition_retains_the_full_integer_sum_residue
    (sourceSignedMagnitudeProductWords left f).1 (sourceSignedMagnitudeProductWords right g).1 equalProducts
  rw [first] at added
  have leftValue := TransferBlstArmInverseSignedWordMultiply01.original_coded_factor_word_preparation_and_partial_products_derive_the_entire_signed_product_residue
    left f fLower fUpper leftNonzero
  have rightValue := TransferBlstArmInverseSignedWordMultiply01.original_coded_factor_word_preparation_and_partial_products_derive_the_entire_signed_product_residue
    right g gLower gUpper rightNonzero
  rw [←same] at rightValue
  calc
    _ = ((packWords (sourceSignedMagnitudeProductWords left f).1 : Int) +
        (packWords (sourceSignedMagnitudeProductWords right g).1 : Int)) % ((radix64 ^ (left.length + 1) : Nat) : Int) := added
    _ = _ := by rw [Int.add_emod, leftValue, rightValue, ←Int.add_emod]

set_option pp.all true in
#check @sourceSignedProductSum
#print axioms sourceSignedProductSum
set_option pp.all true in
#check @equal_input_widths_derive_the_full_extra_word_sum_width
#print axioms equal_input_widths_derive_the_full_extra_word_sum_width
set_option pp.all true in
#check @original_two_signed_products_and_word_sum_derive_the_full_linear_combination_residue
#print axioms original_two_signed_products_and_word_sum_derive_the_full_linear_combination_residue
end ShielddSecurity.TransferBlstArmInverseSignedProductSum01
