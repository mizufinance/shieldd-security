import ShielddSecurity.TransferBlstArmInverseWordLoopFactorWords01
import ShielddSecurity.TransferBlstArmInversePackedFactorUpdate01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseCountedRowProgram01
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseWordLoopFactorWords01 (sourceCountedInputFactorWords)
open TransferBlstArmInversePackedInputRow01 (sourceSelectFactorWordRow)
open TransferBlstArmInversePackedRowProgram01 (sourceWordFactorRowSum sourcePackedRowWordSum
  sourcePackedRowMagnitudeWords sourcePackedMagnitudeWordBatch)
open TransferBlstArmInversePackedFactorUpdate01 (sourcePackedRowCorrectedFactorWords)
open TransferBlstArmInverseSignedWordPrepare01 (sourceMaskPreparedWords)
open TransferBlstArmInverseExtrChain01 (sourceExtractChain)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
open TransferBlstArmInverseFactorSignCorrection01 (sourceExternalFactorSignCorrection)
open TransferBlstArmInverseWordRepack01 (sourceFourWordsOfNat)
open TransferBlstArmInverseMagnitudeBatch01 (sourceMagnitudeBatch)
open TransferBlstArmInverseMagnitudeRows01 (sourceMagnitudeSign)
open TransferBlstArmInverseOriginalRowWords01 (sourceOriginalFactorRow)
open TransferBlstArmInverseOriginalRowMagnitude01 (sourceOriginalRowQuotient)
open TransferBlstArmInverseSignedWord01 (sourceSignedWordMeaning)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords)
attribute [local irreducible] sourceCountedInputFactorWords sourceSelectFactorWordRow sourceWordFactorRowSum
  sourcePackedRowWordSum sourcePackedRowMagnitudeWords sourcePackedMagnitudeWordBatch sourcePackedRowCorrectedFactorWords
  sourceMaskPreparedWords sourceExtractChain sourceFactorSignMask sourceExternalFactorSignCorrection
  sourceFourWordsOfNat sourceMagnitudeBatch sourceMagnitudeSign sourceOriginalFactorRow sourceOriginalRowQuotient sourceSignedWordMeaning

/-! Original approximation words, explicit UInt64 counter/decrement/zero
test and packed updates now feed both source row programs. Entire magnitude
and corrected factor outputs are inherited from the qualified arithmetic
proofs. Accumulated coefficient words and compiled ISA/ABI remain open. -/

def sourceCountedRowFactorWords (second : Bool) (a b : SourceFourWords) : UInt64 × UInt64 :=
  sourceSelectFactorWordRow second (sourceCountedInputFactorWords a b)

def sourceCountedRowWordSum (second : Bool) (a b : SourceFourWords) : List UInt64 × Bool :=
  sourceWordFactorRowSum [a.w0, a.w1, a.w2, a.w3] [b.w0, b.w1, b.w2, b.w3]
    (sourceCountedRowFactorWords second a b)

theorem original_counted_factor_words_feed_the_entire_qualified_source_row_sum
    (second : Bool) (a b : SourceFourWords) :
    sourceCountedRowWordSum second a b = sourcePackedRowWordSum second a b := by
  unfold sourceCountedRowWordSum sourceCountedRowFactorWords sourcePackedRowWordSum
  rw [TransferBlstArmInverseWordLoopFactorWords01.selecting_either_counted_source_loop_row_produces_both_entire_existing_factor_words]

attribute [local irreducible] sourceCountedRowFactorWords sourceCountedRowWordSum

def sourceCountedRowMagnitudeWords (second : Bool) (a b : SourceFourWords) : List UInt64 × Bool :=
  let shifted := sourceExtractChain 31 (sourceCountedRowWordSum second a b).1
  sourceMaskPreparedWords shifted.1 (sourceFactorSignMask shifted.2)

theorem original_counted_loop_products_carries_and_signs_derive_the_entire_qualified_row_magnitude_program
    (second : Bool) (a b : SourceFourWords) :
    sourceCountedRowMagnitudeWords second a b = sourcePackedRowMagnitudeWords second a b := by
  unfold sourceCountedRowMagnitudeWords sourcePackedRowMagnitudeWords
  simp only [original_counted_factor_words_feed_the_entire_qualified_source_row_sum]

attribute [local irreducible] sourceCountedRowMagnitudeWords

theorem original_counted_loop_word_program_derives_the_entire_original_row_quotient_magnitude
    (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    packWords (sourceCountedRowMagnitudeWords second a b).1 =
      (sourceOriginalRowQuotient 31 second a b).natAbs := by
  rw [original_counted_loop_products_carries_and_signs_derive_the_entire_qualified_row_magnitude_program]
  exact TransferBlstArmInversePackedRowProgram01.original_packed_factor_products_carries_extr_and_sign_correction_derive_the_entire_original_quotient_magnitude second a b oddB

def sourceCountedMagnitudeWordBatch (input : Nat × Nat) : List UInt64 × List UInt64 :=
  let a := sourceFourWordsOfNat input.1
  let b := sourceFourWordsOfNat input.2
  ((sourceCountedRowMagnitudeWords false a b).1, (sourceCountedRowMagnitudeWords true a b).1)

theorem original_counted_loop_word_programs_derive_both_entire_qualified_source_word_batch_outputs
    (input : Nat × Nat) : sourceCountedMagnitudeWordBatch input = sourcePackedMagnitudeWordBatch input := by
  let a := sourceFourWordsOfNat input.1
  let b := sourceFourWordsOfNat input.2
  have complete := TransferBlstArmInversePackedRowProgram01.two_symbolic_output_functions_equal_at_every_row_derive_the_entire_pair
    (fun second => (sourceCountedRowMagnitudeWords second a b).1)
    (fun second => (sourcePackedRowMagnitudeWords second a b).1)
    (fun second => congrArg Prod.fst
      (original_counted_loop_products_carries_and_signs_derive_the_entire_qualified_row_magnitude_program second a b))
  unfold sourceCountedMagnitudeWordBatch sourcePackedMagnitudeWordBatch
  exact complete

attribute [local irreducible] sourceCountedMagnitudeWordBatch

theorem original_counted_loop_full_word_program_derives_both_entire_magnitude_batch_values
    (input : Nat × Nat) (odd : input.2 % 2 = 1) :
    (packWords (sourceCountedMagnitudeWordBatch input).1,
     packWords (sourceCountedMagnitudeWordBatch input).2) = sourceMagnitudeBatch input := by
  rw [original_counted_loop_word_programs_derive_both_entire_qualified_source_word_batch_outputs]
  exact TransferBlstArmInversePackedRowProgram01.original_packed_register_products_carries_shifts_and_signs_derive_both_entire_magnitude_batch_values input odd

def sourceCountedRowCorrectedFactorWords (second : Bool) (a b : SourceFourWords) : UInt64 × UInt64 :=
  let factors := sourceCountedRowFactorWords second a b
  let mask := sourceFactorSignMask (sourceExtractChain 31 (sourceCountedRowWordSum second a b).1).2
  (sourceExternalFactorSignCorrection factors.1 mask, sourceExternalFactorSignCorrection factors.2 mask)

theorem original_counted_loop_factor_words_and_sum_top_mask_derive_the_entire_qualified_corrected_factor_program
    (second : Bool) (a b : SourceFourWords) :
    sourceCountedRowCorrectedFactorWords second a b = sourcePackedRowCorrectedFactorWords second a b := by
  unfold sourceCountedRowCorrectedFactorWords sourceCountedRowFactorWords sourcePackedRowCorrectedFactorWords
  simp only [TransferBlstArmInverseWordLoopFactorWords01.selecting_either_counted_source_loop_row_produces_both_entire_existing_factor_words,
    original_counted_factor_words_feed_the_entire_qualified_source_row_sum]

attribute [local irreducible] sourceCountedRowCorrectedFactorWords

theorem original_counted_loop_word_program_derives_both_entire_signed_corrected_coefficients
    (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    sourceSignedWordMeaning (sourceCountedRowCorrectedFactorWords second a b).1 =
      sourceMagnitudeSign (sourceOriginalRowQuotient 31 second a b) * (sourceOriginalFactorRow 31 second a b).1 ∧
    sourceSignedWordMeaning (sourceCountedRowCorrectedFactorWords second a b).2 =
      sourceMagnitudeSign (sourceOriginalRowQuotient 31 second a b) * (sourceOriginalFactorRow 31 second a b).2 := by
  simp only [original_counted_loop_factor_words_and_sum_top_mask_derive_the_entire_qualified_corrected_factor_program]
  exact TransferBlstArmInversePackedFactorUpdate01.original_packed_register_factor_words_and_top_mask_derive_both_entire_signed_coefficients second a b oddB

set_option pp.all true in
#check @sourceCountedRowFactorWords
#print axioms sourceCountedRowFactorWords
set_option pp.all true in
#check @sourceCountedRowWordSum
#print axioms sourceCountedRowWordSum
set_option pp.all true in
#check @original_counted_factor_words_feed_the_entire_qualified_source_row_sum
#print axioms original_counted_factor_words_feed_the_entire_qualified_source_row_sum
set_option pp.all true in
#check @sourceCountedRowMagnitudeWords
#print axioms sourceCountedRowMagnitudeWords
set_option pp.all true in
#check @original_counted_loop_products_carries_and_signs_derive_the_entire_qualified_row_magnitude_program
#print axioms original_counted_loop_products_carries_and_signs_derive_the_entire_qualified_row_magnitude_program
set_option pp.all true in
#check @original_counted_loop_word_program_derives_the_entire_original_row_quotient_magnitude
#print axioms original_counted_loop_word_program_derives_the_entire_original_row_quotient_magnitude
set_option pp.all true in
#check @sourceCountedMagnitudeWordBatch
#print axioms sourceCountedMagnitudeWordBatch
set_option pp.all true in
#check @original_counted_loop_word_programs_derive_both_entire_qualified_source_word_batch_outputs
#print axioms original_counted_loop_word_programs_derive_both_entire_qualified_source_word_batch_outputs
set_option pp.all true in
#check @original_counted_loop_full_word_program_derives_both_entire_magnitude_batch_values
#print axioms original_counted_loop_full_word_program_derives_both_entire_magnitude_batch_values
set_option pp.all true in
#check @sourceCountedRowCorrectedFactorWords
#print axioms sourceCountedRowCorrectedFactorWords
set_option pp.all true in
#check @original_counted_loop_factor_words_and_sum_top_mask_derive_the_entire_qualified_corrected_factor_program
#print axioms original_counted_loop_factor_words_and_sum_top_mask_derive_the_entire_qualified_corrected_factor_program
set_option pp.all true in
#check @original_counted_loop_word_program_derives_both_entire_signed_corrected_coefficients
#print axioms original_counted_loop_word_program_derives_both_entire_signed_corrected_coefficients
end ShielddSecurity.TransferBlstArmInverseCountedRowProgram01
