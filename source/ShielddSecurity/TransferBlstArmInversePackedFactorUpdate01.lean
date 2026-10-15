import ShielddSecurity.TransferBlstArmInversePackedRowProgram01
import ShielddSecurity.TransferBlstArmInverseRowFactorCorrection01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePackedFactorUpdate01
open TransferBlstArmInversePackedInputRow01 (sourceOriginalInputFactorWords sourceFactorRowCodes)
open TransferBlstArmInversePackedRowProgram01 (sourcePackedRowWordSum)
open TransferBlstArmInverseOriginalRowWords01 (sourceOriginalFactorRow sourceOriginalRowWordSum)
open TransferBlstArmInverseOriginalRowMagnitude01 (sourceOriginalRowQuotient)
open TransferBlstArmInverseRowFactorCorrection01 (sourceOriginalCorrectedFactorWords)
open TransferBlstArmInverseFactorSignCorrection01 (sourceExternalFactorSignCorrection)
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode sourceSignedWordMeaning)
open TransferBlstArmInverseMagnitudeRows01 (sourceMagnitudeSign)
open TransferBlstArmInverseExtrChain01 (sourceExtractChain)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords)
attribute [local irreducible] sourceOriginalInputFactorWords sourceFactorRowCodes sourcePackedRowWordSum
  sourceOriginalFactorRow sourceOriginalRowWordSum sourceOriginalRowQuotient sourceOriginalCorrectedFactorWords
  sourceExternalFactorSignCorrection sourceSignedWordCode sourceSignedWordMeaning sourceExtractChain sourceFactorSignMask

/-! The factor words supplied by the original packed recurrence are corrected
by the top-word sign produced by their full source word sum. Both exact codes
and entire signed coefficients follow. UInt64 loop control, coefficient-word
accumulation, private input origins and compiled ISA/ABI remain open. -/

def sourcePackedRowCorrectedFactorWords (second : Bool) (a b : SourceFourWords) : UInt64 × UInt64 :=
  let factors := sourceOriginalInputFactorWords second a b
  let mask := sourceFactorSignMask (sourceExtractChain 31 (sourcePackedRowWordSum second a b).1).2
  (sourceExternalFactorSignCorrection factors.1 mask, sourceExternalFactorSignCorrection factors.2 mask)

theorem original_produced_packed_factor_words_and_sum_top_mask_derive_the_entire_qualified_corrected_factor_word_program
    (second : Bool) (a b : SourceFourWords) :
    sourcePackedRowCorrectedFactorWords second a b = sourceOriginalCorrectedFactorWords second a b := by
  unfold sourcePackedRowCorrectedFactorWords sourceOriginalCorrectedFactorWords
  simp only [TransferBlstArmInversePackedInputRow01.original_input_window_packed_registers_and_slot_decoders_produce_both_entire_factor_row_codes,
    TransferBlstArmInversePackedRowProgram01.original_packed_factor_words_feed_the_entire_original_signed_row_word_sum,
    sourceFactorRowCodes]

attribute [local irreducible] sourcePackedRowCorrectedFactorWords

theorem original_packed_register_factor_words_and_top_mask_derive_both_entire_sign_corrected_integer_codes
    (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    sourcePackedRowCorrectedFactorWords second a b =
      (sourceSignedWordCode (sourceMagnitudeSign (sourceOriginalRowQuotient 31 second a b) * (sourceOriginalFactorRow 31 second a b).1),
       sourceSignedWordCode (sourceMagnitudeSign (sourceOriginalRowQuotient 31 second a b) * (sourceOriginalFactorRow 31 second a b).2)) := by
  rw [original_produced_packed_factor_words_and_sum_top_mask_derive_the_entire_qualified_corrected_factor_word_program]
  exact TransferBlstArmInverseRowFactorCorrection01.original_word_sum_top_asr_and_factor_eor_sub_derive_both_complete_corrected_factor_codes second a b oddB

theorem original_packed_register_factor_words_and_top_mask_derive_both_entire_signed_coefficients
    (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    sourceSignedWordMeaning (sourcePackedRowCorrectedFactorWords second a b).1 =
      sourceMagnitudeSign (sourceOriginalRowQuotient 31 second a b) * (sourceOriginalFactorRow 31 second a b).1 ∧
    sourceSignedWordMeaning (sourcePackedRowCorrectedFactorWords second a b).2 =
      sourceMagnitudeSign (sourceOriginalRowQuotient 31 second a b) * (sourceOriginalFactorRow 31 second a b).2 := by
  simp only [original_produced_packed_factor_words_and_sum_top_mask_derive_the_entire_qualified_corrected_factor_word_program]
  exact TransferBlstArmInverseRowFactorCorrection01.original_word_sum_top_asr_and_factor_eor_sub_derive_both_entire_signed_coefficients second a b oddB

set_option pp.all true in
#check @sourcePackedRowCorrectedFactorWords
#print axioms sourcePackedRowCorrectedFactorWords
set_option pp.all true in
#check @original_produced_packed_factor_words_and_sum_top_mask_derive_the_entire_qualified_corrected_factor_word_program
#print axioms original_produced_packed_factor_words_and_sum_top_mask_derive_the_entire_qualified_corrected_factor_word_program
set_option pp.all true in
#check @original_packed_register_factor_words_and_top_mask_derive_both_entire_sign_corrected_integer_codes
#print axioms original_packed_register_factor_words_and_top_mask_derive_both_entire_sign_corrected_integer_codes
set_option pp.all true in
#check @original_packed_register_factor_words_and_top_mask_derive_both_entire_signed_coefficients
#print axioms original_packed_register_factor_words_and_top_mask_derive_both_entire_signed_coefficients
end ShielddSecurity.TransferBlstArmInversePackedFactorUpdate01
