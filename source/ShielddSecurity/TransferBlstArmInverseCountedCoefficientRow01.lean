import ShielddSecurity.TransferBlstArmInverseCoefficientRowResidue01
import ShielddSecurity.TransferBlstArmInverseCountedRowProgram01
import ShielddSecurity.TransferBlstArmInverseRowNorm01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseCountedCoefficientRow01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseCoefficientRowResidue01 (sourceCoefficientRowWords)
open TransferBlstArmInverseCountedRowProgram01 (sourceCountedRowCorrectedFactorWords)
open TransferBlstArmInverseOriginalRowWords01 (sourceOriginalFactorRow)
open TransferBlstArmInverseOriginalRowMagnitude01 (sourceOriginalRowQuotient)
open TransferBlstArmInverseMagnitudeRows01 (sourceMagnitudeSign)
open TransferBlstArmInverseSignedWord01 (sourceSignedWordMeaning)
open TransferBlstArmInverseSignedProductDecode01 (sourceSignedRadixDecode)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords)
attribute [local irreducible] sourceCoefficientRowWords sourceCountedRowCorrectedFactorWords
  sourceOriginalFactorRow sourceOriginalRowQuotient sourceMagnitudeSign sourceSignedWordMeaning

/-! The counted original word loop and row-result signs supply the factor
words for an entire coefficient update. The original row norm derives its
integer range from input coefficient bounds. The assembly's compressed
operand layout, split product schedule and topmost stored word remain open. -/

def sourceSelectedCorrectedFactors (count : Nat) (second : Bool) (a b : SourceFourWords) : Int × Int :=
  let row := sourceOriginalFactorRow count second a b
  let sign := sourceMagnitudeSign (sourceOriginalRowQuotient count second a b)
  (sign * row.1, sign * row.2)

theorem the_counted_original_word_program_derives_both_entire_selected_corrected_factors
    (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    (sourceSignedWordMeaning (sourceCountedRowCorrectedFactorWords second a b).1,
     sourceSignedWordMeaning (sourceCountedRowCorrectedFactorWords second a b).2) =
      sourceSelectedCorrectedFactors 31 second a b := by
  have decoded := TransferBlstArmInverseCountedRowProgram01.original_counted_loop_word_program_derives_both_entire_signed_corrected_coefficients second a b oddB
  unfold sourceSelectedCorrectedFactors
  exact Prod.ext decoded.1 decoded.2

theorem every_original_selected_corrected_factor_row_retains_its_entire_radix_power_norm
    (count : Nat) (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    (sourceSelectedCorrectedFactors count second a b).1.natAbs +
      (sourceSelectedCorrectedFactors count second a b).2.natAbs ≤ 2 ^ count := by
  have contract := TransferBlstArmInverseOriginalRowWords01.original_window_factor_rows_derive_all_source_product_bounds_and_nonzero_origins count second a b oddB
  unfold sourceSelectedCorrectedFactors
  rw [TransferBlstArmInverseRowNorm01.simultaneous_source_row_sign_correction_preserves_its_entire_row_sum]
  exact contract.norm

attribute [local irreducible] sourceSelectedCorrectedFactors

theorem bounded_input_coefficients_and_an_entire_combining_row_norm_bound_the_full_update
    (u v f g : Int) (oldBound rowBound : Nat)
    (left : u.natAbs ≤ oldBound) (right : v.natAbs ≤ oldBound)
    (row : f.natAbs + g.natAbs ≤ rowBound) :
    (u * f + v * g).natAbs ≤ oldBound * rowBound := by
  have combined := TransferBlstArmInverseRowNorm01.two_bounded_rows_and_a_bounded_combining_row_derive_the_product_row_sum_bound
    u 0 v 0 f g oldBound rowBound
    (by simpa only [Int.natAbs_zero, Nat.add_zero] using left)
    (by simpa only [Int.natAbs_zero, Nat.add_zero] using right) row
  simp only [Int.mul_zero, Int.add_zero, Int.natAbs_zero, Nat.add_zero] at combined
  have reorder : u * f + v * g = f * u + g * v := by ring1
  rw [reorder]
  exact combined

def sourceCountedCoefficientRowWords (second : Bool) (a b : SourceFourWords)
    (left right : List UInt64) : List UInt64 × Bool :=
  sourceCoefficientRowWords left right (sourceCountedRowCorrectedFactorWords second a b)

theorem the_counted_source_coefficient_word_update_has_the_entire_original_corrected_row_residue
    (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1)
    (left right : List UInt64) (u v : Int) (same : left.length = right.length)
    (leftInput : (packWords left : Int) % ((radix64 ^ left.length : Nat) : Int) = u % ((radix64 ^ left.length : Nat) : Int))
    (rightInput : (packWords right : Int) % ((radix64 ^ left.length : Nat) : Int) = v % ((radix64 ^ left.length : Nat) : Int)) :
    (packWords (sourceCountedCoefficientRowWords second a b left right).1 : Int) % ((radix64 ^ left.length : Nat) : Int) =
      (u * (sourceSelectedCorrectedFactors 31 second a b).1 +
       v * (sourceSelectedCorrectedFactors 31 second a b).2) % ((radix64 ^ left.length : Nat) : Int) := by
  have factors := the_counted_original_word_program_derives_both_entire_selected_corrected_factors second a b oddB
  have first := congrArg Prod.fst factors
  have last := congrArg Prod.snd factors
  have result := TransferBlstArmInverseCoefficientRowResidue01.source_coefficient_words_with_exact_input_residues_derive_the_entire_integer_row_residue
    left right (sourceCountedRowCorrectedFactorWords second a b) u v same leftInput rightInput
  dsimp only at first last
  rw [first, last] at result
  exact result

attribute [local irreducible] sourceCountedCoefficientRowWords

theorem original_counted_source_coefficient_words_recover_the_entire_row_from_derived_norm_capacity
    (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1)
    (left right : List UInt64) (u v half : Int) (oldBound : Nat)
    (same : left.length = right.length)
    (capacity : ((radix64 ^ left.length : Nat) : Int) = 2 * half)
    (leftInput : (packWords left : Int) % (2 * half) = u % (2 * half))
    (rightInput : (packWords right : Int) % (2 * half) = v % (2 * half))
    (leftBound : u.natAbs ≤ oldBound) (rightBound : v.natAbs ≤ oldBound)
    (room : ((oldBound * 2 ^ 31 : Nat) : Int) < half) :
    sourceSignedRadixDecode half (packWords (sourceCountedCoefficientRowWords second a b left right).1 : Int) =
      u * (sourceSelectedCorrectedFactors 31 second a b).1 +
      v * (sourceSelectedCorrectedFactors 31 second a b).2 := by
  let row := sourceSelectedCorrectedFactors 31 second a b
  let value := u * row.1 + v * row.2
  have norm := every_original_selected_corrected_factor_row_retains_its_entire_radix_power_norm 31 second a b oddB
  have bounded := bounded_input_coefficients_and_an_entire_combining_row_norm_bound_the_full_update
    u v row.1 row.2 oldBound (2 ^ 31) leftBound rightBound norm
  have castBound : (value.natAbs : Int) ≤ ((oldBound * 2 ^ 31 : Nat) : Int) := by exact_mod_cast bounded
  have upperValue := Int.le_natAbs (a := value)
  have lowerValue := Int.le_natAbs (a := -value)
  rw [Int.natAbs_neg] at lowerValue
  have lower : -half ≤ value := by omega
  have upper : value < half := by omega
  have factors := the_counted_original_word_program_derives_both_entire_selected_corrected_factors second a b oddB
  have first := congrArg Prod.fst factors
  have last := congrArg Prod.snd factors
  dsimp only at first last
  have lowerWords : -half ≤ u * sourceSignedWordMeaning (sourceCountedRowCorrectedFactorWords second a b).1 +
      v * sourceSignedWordMeaning (sourceCountedRowCorrectedFactorWords second a b).2 := by
    rw [first, last]
    exact lower
  have upperWords : u * sourceSignedWordMeaning (sourceCountedRowCorrectedFactorWords second a b).1 +
      v * sourceSignedWordMeaning (sourceCountedRowCorrectedFactorWords second a b).2 < half := by
    rw [first, last]
    exact upper
  have result := TransferBlstArmInverseCoefficientRowResidue01.bounded_entire_integer_rows_are_recovered_from_the_source_coefficient_word_program
    left right (sourceCountedRowCorrectedFactorWords second a b) u v half same capacity leftInput rightInput lowerWords upperWords
  rw [first, last] at result
  unfold sourceCountedCoefficientRowWords
  exact result

set_option pp.all true in
#check @sourceSelectedCorrectedFactors
#print axioms sourceSelectedCorrectedFactors
set_option pp.all true in
#check @the_counted_original_word_program_derives_both_entire_selected_corrected_factors
#print axioms the_counted_original_word_program_derives_both_entire_selected_corrected_factors
set_option pp.all true in
#check @every_original_selected_corrected_factor_row_retains_its_entire_radix_power_norm
#print axioms every_original_selected_corrected_factor_row_retains_its_entire_radix_power_norm
set_option pp.all true in
#check @bounded_input_coefficients_and_an_entire_combining_row_norm_bound_the_full_update
#print axioms bounded_input_coefficients_and_an_entire_combining_row_norm_bound_the_full_update
set_option pp.all true in
#check @sourceCountedCoefficientRowWords
#print axioms sourceCountedCoefficientRowWords
set_option pp.all true in
#check @the_counted_source_coefficient_word_update_has_the_entire_original_corrected_row_residue
#print axioms the_counted_source_coefficient_word_update_has_the_entire_original_corrected_row_residue
set_option pp.all true in
#check @original_counted_source_coefficient_words_recover_the_entire_row_from_derived_norm_capacity
#print axioms original_counted_source_coefficient_words_recover_the_entire_row_from_derived_norm_capacity
end ShielddSecurity.TransferBlstArmInverseCountedCoefficientRow01
