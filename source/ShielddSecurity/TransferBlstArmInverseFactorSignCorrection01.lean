import ShielddSecurity.TransferBlstArmInverseSignedWord01
import ShielddSecurity.TransferBlstArmInverseMagnitudeRows01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseFactorSignCorrection01
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode sourceSignedWordMeaning)
open TransferBlstArmInverseMagnitudeRows01 (sourceMagnitudeSign)

/-! Source EOR/SUB updates a factor using the external row-result sign mask.
The mask origin, original factor-register origin and compiled instructions
remain separate. The word code identity holds for every integer residue. -/

def sourceExternalFactorSignCorrection (word mask : UInt64) : UInt64 :=
  (word ^^^ mask) - mask

theorem the_source_signed_word_code_is_the_entire_standard_integer_word_conversion
    (value : Int) : sourceSignedWordCode value = UInt64.ofInt value := by rfl

theorem an_external_zero_or_all_ones_mask_derives_the_entire_word_identity_or_negation
    (negative : Prop) [Decidable negative] (word : UInt64) :
    sourceExternalFactorSignCorrection word (if negative then (-1 : UInt64) else 0) =
      if negative then -word else word := by
  by_cases sign : negative
  · simp only [if_pos sign]
    rw [sourceExternalFactorSignCorrection, UInt64.xor_neg_one, UInt64.sub_neg]
    apply UInt64.toBitVec_inj.mp
    simpa only [UInt64.toBitVec_add, UInt64.toBitVec_not, UInt64.toBitVec_neg] using
      (BitVec.neg_eq_not_add word.toBitVec).symm
  · simp only [if_neg sign, sourceExternalFactorSignCorrection, UInt64.xor_zero, UInt64.sub_zero]

theorem the_external_row_result_sign_correction_derives_the_complete_corrected_integer_factor_code
    (factor value : Int) :
    sourceExternalFactorSignCorrection (sourceSignedWordCode factor)
      (if value < 0 then (-1 : UInt64) else 0) = sourceSignedWordCode (sourceMagnitudeSign value * factor) := by
  rw [an_external_zero_or_all_ones_mask_derives_the_entire_word_identity_or_negation]
  by_cases negative : value < 0
  · simp only [if_pos negative, sourceMagnitudeSign, Int.neg_one_mul,
      the_source_signed_word_code_is_the_entire_standard_integer_word_conversion, UInt64.ofInt_neg]
  · simp only [if_neg negative, sourceMagnitudeSign, Int.one_mul]

set_option pp.all true in
#check @sourceExternalFactorSignCorrection
#print axioms sourceExternalFactorSignCorrection
set_option pp.all true in
#check @the_source_signed_word_code_is_the_entire_standard_integer_word_conversion
#print axioms the_source_signed_word_code_is_the_entire_standard_integer_word_conversion
set_option pp.all true in
#check @an_external_zero_or_all_ones_mask_derives_the_entire_word_identity_or_negation
#print axioms an_external_zero_or_all_ones_mask_derives_the_entire_word_identity_or_negation
set_option pp.all true in
#check @the_external_row_result_sign_correction_derives_the_complete_corrected_integer_factor_code
#print axioms the_external_row_result_sign_correction_derives_the_complete_corrected_integer_factor_code
end ShielddSecurity.TransferBlstArmInverseFactorSignCorrection01
