import ShielddSecurity.TransferBlstArmInverseRowWordOperation01
import ShielddSecurity.TransferBlstArmInverseShiftAbsolute01
import ShielddSecurity.TransferBlstArmInverseBatchRange01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseOriginalRowMagnitude01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseOriginalRowWords01 (sourceSelectFactorRow sourceOriginalFactorRow sourceOriginalRowWordSum)
open TransferBlstArmInverseExtrChain01 (sourceExtractChain)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
open TransferBlstArmInverseSignedWordPrepare01 (sourceMaskPreparedWords)
attribute [local irreducible] sourceFactorWalk sourceOriginalFactorRow sourceOriginalRowWordSum
  sourceActualFactorQuotients sourceExtractChain sourceFactorSignMask sourceMaskPreparedWords

/-! Original batch range supplies the magnitude bound for the complete source
signed multiply/carry/EXTR31/top-ASR/absolute-correction path. The factors are
the original recurrence coefficients; packed factor-register and compiled
instruction correspondence remain separate obligations. -/

theorem generic_selected_row_division_is_the_exact_selected_full_quotient
    (second : Bool) (f0 g0 f1 g1 inputA inputB divisor : Int) :
    (inputA * (sourceSelectFactorRow second f0 g0 f1 g1).1 +
      inputB * (sourceSelectFactorRow second f0 g0 f1 g1).2) / divisor =
      if second then (f1 * inputA + g1 * inputB) / divisor else (f0 * inputA + g0 * inputB) / divisor := by
  cases second with
  | false =>
    change (inputA * f0 + inputB * g0) / divisor = (f0 * inputA + g0 * inputB) / divisor
    congr 1
    ring1
  | true =>
    change (inputA * f1 + inputB * g1) / divisor = (f1 * inputA + g1 * inputB) / divisor
    congr 1
    ring1

theorem either_bounded_integer_choice_retains_the_entire_magnitude_bound
    (second : Bool) (first last : Int) (capacity : Nat)
    (firstSmall : first.natAbs < capacity) (lastSmall : last.natAbs < capacity) :
    (if second then last else first).natAbs < capacity := by
  cases second with
  | false => exact firstSmall
  | true => exact lastSmall

attribute [local irreducible] sourceSelectFactorRow

def sourceOriginalRowQuotient (count : Nat) (second : Bool) (a b : SourceFourWords) : Int :=
  let row := sourceOriginalFactorRow count second a b
  ((sourcePackedFourWords a : Int) * row.1 + (sourcePackedFourWords b : Int) * row.2) / ((2 : Int) ^ count)

theorem the_original_selected_row_quotient_is_the_original_full_input_quotient
    (count : Nat) (second : Bool) (a b : SourceFourWords) :
    sourceOriginalRowQuotient count second a b =
      let actual := sourceActualFactorQuotients count
        (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
        (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
      if second then actual.2 else actual.1 := by
  unfold sourceOriginalRowQuotient sourceOriginalFactorRow sourceActualFactorQuotients
  let factors := sourceFactorWalk count (sourceFactorInitial
    (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
    (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))
  exact generic_selected_row_division_is_the_exact_selected_full_quotient second
    factors.f0 factors.g0 factors.f1 factors.g1 (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int) ((2 : Int) ^ count)

attribute [local irreducible] sourceOriginalRowQuotient

theorem original_batch_range_derives_the_entire_source_selected_quotient_magnitude_bound
    (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    (sourceOriginalRowQuotient 31 second a b).natAbs < radix64 ^ 4 := by
  have both := TransferBlstArmInverseBatchRange01.every_original31_step_full_output_magnitude_fits_four_words a b oddB
  dsimp only at both
  have power : radix64 ^ 4 = (2 : Nat) ^ 256 := by simp only [radix64, ←Nat.pow_mul]
  rw [power, the_original_selected_row_quotient_is_the_original_full_input_quotient]
  exact either_bounded_integer_choice_retains_the_entire_magnitude_bound second _ _ _ both.1 both.2

def sourceOriginalRowMagnitudeWords (second : Bool) (a b : SourceFourWords) : List UInt64 × Bool :=
  let shifted := sourceExtractChain 31 (sourceOriginalRowWordSum second a b).1
  sourceMaskPreparedWords shifted.1 (sourceFactorSignMask shifted.2)

theorem original_source_signed_products_carry_extr_asr_and_absolute_correction_derive_the_entire_quotient_magnitude
    (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    packWords (sourceOriginalRowMagnitudeWords second a b).1 =
      (sourceOriginalRowQuotient 31 second a b).natAbs := by
  have decoded := TransferBlstArmInverseRowWordOperation01.original_window_factor_rows_and_source_word_products_derive_the_entire_signed_row_numerator
    second a b oddB
  have width := TransferBlstArmInverseRowWordOperation01.every_original_source_row_word_sum_retains_exactly_five_words second a b
  have bounded := original_batch_range_derives_the_entire_source_selected_quotient_magnitude_bound second a b oddB
  unfold sourceOriginalRowQuotient at bounded ⊢
  unfold sourceOriginalRowMagnitudeWords
  exact TransferBlstArmInverseShiftAbsolute01.source_extr_top_asr_and_word_absolute_correction_derive_the_entire_quotient_magnitude
    (sourceOriginalRowWordSum second a b).1 4 31
    ((sourcePackedFourWords a : Int) * (sourceOriginalFactorRow 31 second a b).1 +
      (sourcePackedFourWords b : Int) * (sourceOriginalFactorRow 31 second a b).2)
    width (by decide) (by decide) decoded bounded

set_option pp.all true in
#check @generic_selected_row_division_is_the_exact_selected_full_quotient
#print axioms generic_selected_row_division_is_the_exact_selected_full_quotient
set_option pp.all true in
#check @either_bounded_integer_choice_retains_the_entire_magnitude_bound
#print axioms either_bounded_integer_choice_retains_the_entire_magnitude_bound
set_option pp.all true in
#check @sourceOriginalRowQuotient
#print axioms sourceOriginalRowQuotient
set_option pp.all true in
#check @the_original_selected_row_quotient_is_the_original_full_input_quotient
#print axioms the_original_selected_row_quotient_is_the_original_full_input_quotient
set_option pp.all true in
#check @original_batch_range_derives_the_entire_source_selected_quotient_magnitude_bound
#print axioms original_batch_range_derives_the_entire_source_selected_quotient_magnitude_bound
set_option pp.all true in
#check @sourceOriginalRowMagnitudeWords
#print axioms sourceOriginalRowMagnitudeWords
set_option pp.all true in
#check @original_source_signed_products_carry_extr_asr_and_absolute_correction_derive_the_entire_quotient_magnitude
#print axioms original_source_signed_products_carry_extr_asr_and_absolute_correction_derive_the_entire_quotient_magnitude
end ShielddSecurity.TransferBlstArmInverseOriginalRowMagnitude01
