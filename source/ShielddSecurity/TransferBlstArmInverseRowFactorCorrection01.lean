import ShielddSecurity.TransferBlstArmInverseRowSignMask01
import ShielddSecurity.TransferBlstArmInverseFactorSignCorrection01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseRowFactorCorrection01
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode sourceSignedWordMeaning)
open TransferBlstArmInverseMagnitudeRows01 (sourceMagnitudeSign)
open TransferBlstArmInverseFactorSignCorrection01 (sourceExternalFactorSignCorrection)
open TransferBlstArmInverseOriginalRowWords01 (sourceOriginalFactorRow sourceOriginalRowWordSum)
open TransferBlstArmInverseOriginalRowMagnitude01 (sourceOriginalRowQuotient)
open TransferBlstArmInverseExtrChain01 (sourceExtractChain)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
attribute [local irreducible] sourceSignedWordCode sourceSignedWordMeaning sourceExternalFactorSignCorrection
  sourceOriginalFactorRow sourceOriginalRowWordSum sourceOriginalRowQuotient sourceExtractChain sourceFactorSignMask

/-! Both source factor EOR/SUB updates use the sign mask produced by the
original signed row word sum. Exact corrected integer codes and decoded
coefficients follow from the original row norm. Packed input factor word
origins, accumulated coefficient updates and compiled execution stay open. -/

theorem an_exact_external_row_mask_derives_both_complete_corrected_factor_codes
    (f g value : Int) (mask : UInt64)
    (origin : mask = if value < 0 then (-1 : UInt64) else 0) :
    (sourceExternalFactorSignCorrection (sourceSignedWordCode f) mask,
      sourceExternalFactorSignCorrection (sourceSignedWordCode g) mask) =
      (sourceSignedWordCode (sourceMagnitudeSign value * f), sourceSignedWordCode (sourceMagnitudeSign value * g)) := by
  simp only [origin]
  exact Prod.ext
    (TransferBlstArmInverseFactorSignCorrection01.the_external_row_result_sign_correction_derives_the_complete_corrected_integer_factor_code f value)
    (TransferBlstArmInverseFactorSignCorrection01.the_external_row_result_sign_correction_derives_the_complete_corrected_integer_factor_code g value)

theorem the_source_row_result_sign_preserves_each_entire_factor_magnitude
    (value factor : Int) : (sourceMagnitudeSign value * factor).natAbs = factor.natAbs := by
  by_cases negative : value < 0
  · simp only [sourceMagnitudeSign, if_pos negative, Int.neg_one_mul, Int.natAbs_neg]
  · simp only [sourceMagnitudeSign, if_neg negative, Int.one_mul]

theorem a_31_step_bounded_row_derives_signed64_bounds_for_both_sign_corrected_factors
    (f g value : Int) (row : f.natAbs + g.natAbs ≤ 2 ^ 31) :
    (-9223372036854775808 ≤ sourceMagnitudeSign value * f ∧ sourceMagnitudeSign value * f < 9223372036854775808) ∧
      (-9223372036854775808 ≤ sourceMagnitudeSign value * g ∧ sourceMagnitudeSign value * g < 9223372036854775808) := by
  have corrected : (sourceMagnitudeSign value * f).natAbs + (sourceMagnitudeSign value * g).natAbs ≤ 2 ^ 31 := by
    rw [the_source_row_result_sign_preserves_each_entire_factor_magnitude,
      the_source_row_result_sign_preserves_each_entire_factor_magnitude]
    exact row
  exact TransferBlstArmInverseRowSumDecode01.every_factor_in_a_31_step_bounded_row_fits_the_entire_signed64_range _ _ corrected

def sourceOriginalCorrectedFactorWords (second : Bool)
    (a b : TransferBlstArmInverseWindowSelect01.SourceFourWords) : UInt64 × UInt64 :=
  let row := sourceOriginalFactorRow 31 second a b
  let mask := sourceFactorSignMask (sourceExtractChain 31 (sourceOriginalRowWordSum second a b).1).2
  (sourceExternalFactorSignCorrection (sourceSignedWordCode row.1) mask,
   sourceExternalFactorSignCorrection (sourceSignedWordCode row.2) mask)

theorem original_word_sum_top_asr_and_factor_eor_sub_derive_both_complete_corrected_factor_codes
    (second : Bool) (a b : TransferBlstArmInverseWindowSelect01.SourceFourWords)
    (oddB : b.w0.toNat % 2 = 1) :
    sourceOriginalCorrectedFactorWords second a b =
      (sourceSignedWordCode (sourceMagnitudeSign (sourceOriginalRowQuotient 31 second a b) * (sourceOriginalFactorRow 31 second a b).1),
       sourceSignedWordCode (sourceMagnitudeSign (sourceOriginalRowQuotient 31 second a b) * (sourceOriginalFactorRow 31 second a b).2)) := by
  have mask := TransferBlstArmInverseRowSignMask01.original_row_word_sum_retained_top_asr_derives_the_exact_original_quotient_sign_mask second a b oddB
  unfold sourceOriginalCorrectedFactorWords
  exact an_exact_external_row_mask_derives_both_complete_corrected_factor_codes
    (sourceOriginalFactorRow 31 second a b).1 (sourceOriginalFactorRow 31 second a b).2
    (sourceOriginalRowQuotient 31 second a b) _ mask

attribute [local irreducible] sourceOriginalCorrectedFactorWords

theorem original_word_sum_top_asr_and_factor_eor_sub_derive_both_entire_signed_coefficients
    (second : Bool) (a b : TransferBlstArmInverseWindowSelect01.SourceFourWords)
    (oddB : b.w0.toNat % 2 = 1) :
    sourceSignedWordMeaning (sourceOriginalCorrectedFactorWords second a b).1 =
      sourceMagnitudeSign (sourceOriginalRowQuotient 31 second a b) * (sourceOriginalFactorRow 31 second a b).1 ∧
    sourceSignedWordMeaning (sourceOriginalCorrectedFactorWords second a b).2 =
      sourceMagnitudeSign (sourceOriginalRowQuotient 31 second a b) * (sourceOriginalFactorRow 31 second a b).2 := by
  have row := TransferBlstArmInverseOriginalRowWords01.original_window_factor_rows_derive_all_source_product_bounds_and_nonzero_origins 31 second a b oddB
  have bounds := a_31_step_bounded_row_derives_signed64_bounds_for_both_sign_corrected_factors
    (sourceOriginalFactorRow 31 second a b).1 (sourceOriginalFactorRow 31 second a b).2
    (sourceOriginalRowQuotient 31 second a b) row.norm
  simp only [original_word_sum_top_asr_and_factor_eor_sub_derive_both_complete_corrected_factor_codes second a b oddB]
  exact ⟨TransferBlstArmInverseSignedWord01.original_signed64_code_and_threshold_decode_recover_the_entire_factor_value _ bounds.1.1 bounds.1.2,
    TransferBlstArmInverseSignedWord01.original_signed64_code_and_threshold_decode_recover_the_entire_factor_value _ bounds.2.1 bounds.2.2⟩

set_option pp.all true in
#check @an_exact_external_row_mask_derives_both_complete_corrected_factor_codes
#print axioms an_exact_external_row_mask_derives_both_complete_corrected_factor_codes
set_option pp.all true in
#check @the_source_row_result_sign_preserves_each_entire_factor_magnitude
#print axioms the_source_row_result_sign_preserves_each_entire_factor_magnitude
set_option pp.all true in
#check @a_31_step_bounded_row_derives_signed64_bounds_for_both_sign_corrected_factors
#print axioms a_31_step_bounded_row_derives_signed64_bounds_for_both_sign_corrected_factors
set_option pp.all true in
#check @sourceOriginalCorrectedFactorWords
#print axioms sourceOriginalCorrectedFactorWords
set_option pp.all true in
#check @original_word_sum_top_asr_and_factor_eor_sub_derive_both_complete_corrected_factor_codes
#print axioms original_word_sum_top_asr_and_factor_eor_sub_derive_both_complete_corrected_factor_codes
set_option pp.all true in
#check @original_word_sum_top_asr_and_factor_eor_sub_derive_both_entire_signed_coefficients
#print axioms original_word_sum_top_asr_and_factor_eor_sub_derive_both_entire_signed_coefficients
end ShielddSecurity.TransferBlstArmInverseRowFactorCorrection01
