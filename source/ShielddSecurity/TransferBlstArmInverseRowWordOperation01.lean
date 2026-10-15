import ShielddSecurity.TransferBlstArmInverseOriginalRowWords01
import ShielddSecurity.TransferBlstArmInverseRowSumDecode01
import ShielddSecurity.TransferBlstArmInverseZeroFactorRows01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseRowWordOperation01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorWalk sourceFactorInitial)
open TransferBlstArmInverseSignedProductSum01 (sourceSignedProductSum)
open TransferBlstArmInverseSignedProductDecode01 (sourceSignedRadixDecode)
open TransferBlstArmInverseExtrChain01 (sourceExtractChain)
attribute [local irreducible] sourceFactorWalk sourceSignedProductSum sourceSignedRadixDecode sourceExtractChain

/-! The original four-word window and 31-step factor recurrence supply every
coefficient and negative-input nonzero premise used by source word products.
The resulting sum and EXTR31 residues are arithmetic source correspondences;
packed factor-register origins and compiled instruction execution stay open. -/

open TransferBlstArmInverseOriginalRowWords01 (sourceOriginalFactorRow sourceOriginalRowWordSum original_window_factor_rows_derive_all_source_product_bounds_and_nonzero_origins)
attribute [local irreducible] sourceOriginalFactorRow sourceOriginalRowWordSum

theorem every_original_source_row_word_sum_retains_exactly_five_words
    (second : Bool) (a b : SourceFourWords) :
    (sourceOriginalRowWordSum second a b).1.length = 5 := by
  unfold sourceOriginalRowWordSum
  exact TransferBlstArmInverseSignedProductSum01.equal_input_widths_derive_the_full_extra_word_sum_width
    [a.w0, a.w1, a.w2, a.w3] [b.w0, b.w1, b.w2, b.w3]
    (sourceOriginalFactorRow 31 second a b).1 (sourceOriginalFactorRow 31 second a b).2 rfl

theorem original_window_factor_rows_and_source_word_products_derive_the_entire_signed_row_numerator
    (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    let row := sourceOriginalFactorRow 31 second a b
    sourceSignedRadixDecode ((radix64 ^ 4 * 9223372036854775808 : Nat) : Int)
      (packWords (sourceOriginalRowWordSum second a b).1 : Int) =
        (sourcePackedFourWords a : Int) * row.1 + (sourcePackedFourWords b : Int) * row.2 := by
  unfold sourceOriginalRowWordSum
  have conditions := original_window_factor_rows_derive_all_source_product_bounds_and_nonzero_origins 31 second a b oddB
  dsimp only
  exact TransferBlstArmInverseRowSumDecode01.original_two_signed_products_and_carry_sum_derive_the_entire_31_step_row_integer
    [a.w0, a.w1, a.w2, a.w3] [b.w0, b.w1, b.w2, b.w3]
    (sourceOriginalFactorRow 31 second a b).1 (sourceOriginalFactorRow 31 second a b).2 rfl conditions.norm conditions.negativeNonzero
    (fun _ => conditions.secondPositive)

theorem original_window_factor_rows_and_source_extr31_derive_the_entire_signed_quotient_residue
    (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    let row := sourceOriginalFactorRow 31 second a b
    (packWords (sourceExtractChain 31 (sourceOriginalRowWordSum second a b).1).1 : Int) =
      (((sourcePackedFourWords a : Int) * row.1 + (sourcePackedFourWords b : Int) * row.2) / ((2 : Int) ^ 31)) %
        ((radix64 ^ 4 : Nat) : Int) := by
  have conditions := original_window_factor_rows_derive_all_source_product_bounds_and_nonzero_origins 31 second a b oddB
  dsimp only
  have factors := TransferBlstArmInverseRowSumDecode01.every_factor_in_a_31_step_bounded_row_fits_the_entire_signed64_range
    (sourceOriginalFactorRow 31 second a b).1 (sourceOriginalFactorRow 31 second a b).2 conditions.norm
  have residue := TransferBlstArmInverseSignedProductSum01.original_two_signed_products_and_word_sum_derive_the_full_linear_combination_residue
    [a.w0, a.w1, a.w2, a.w3] [b.w0, b.w1, b.w2, b.w3]
    (sourceOriginalFactorRow 31 second a b).1 (sourceOriginalFactorRow 31 second a b).2 rfl
    factors.1.1 factors.1.2 factors.2.1 factors.2.2 conditions.negativeNonzero (fun _ => conditions.secondPositive)
  have sourceResidue : (packWords (sourceOriginalRowWordSum second a b).1 : Int) % ((radix64 ^ 5 : Nat) : Int) =
      ((sourcePackedFourWords a : Int) * (sourceOriginalFactorRow 31 second a b).1 +
        (sourcePackedFourWords b : Int) * (sourceOriginalFactorRow 31 second a b).2) % ((radix64 ^ 5 : Nat) : Int) := by
    unfold sourceOriginalRowWordSum
    exact residue
  have width := every_original_source_row_word_sum_retains_exactly_five_words second a b
  exact TransferBlstArmInverseSignedExtrQuotient01.the_entire_source_extraction_chain_derives_the_signed_integer_quotient_residue
    (sourceOriginalRowWordSum second a b).1 4 31
    ((sourcePackedFourWords a : Int) * (sourceOriginalFactorRow 31 second a b).1 +
      (sourcePackedFourWords b : Int) * (sourceOriginalFactorRow 31 second a b).2)
    width (by decide) (by decide) sourceResidue

set_option pp.all true in
#check @every_original_source_row_word_sum_retains_exactly_five_words
#print axioms every_original_source_row_word_sum_retains_exactly_five_words
set_option pp.all true in
#check @original_window_factor_rows_and_source_word_products_derive_the_entire_signed_row_numerator
#print axioms original_window_factor_rows_and_source_word_products_derive_the_entire_signed_row_numerator
set_option pp.all true in
#check @original_window_factor_rows_and_source_extr31_derive_the_entire_signed_quotient_residue
#print axioms original_window_factor_rows_and_source_extr31_derive_the_entire_signed_quotient_residue
end ShielddSecurity.TransferBlstArmInverseRowWordOperation01
