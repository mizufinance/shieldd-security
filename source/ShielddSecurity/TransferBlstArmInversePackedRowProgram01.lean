import ShielddSecurity.TransferBlstArmInversePackedInputRow01
import ShielddSecurity.TransferBlstArmInverseWordMagnitudeBatch01
import ShielddSecurity.TransferBlstArmInverseRowFactorCorrection01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePackedRowProgram01
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
open TransferBlstArmInverseFactorMagnitude01 (sourceFactorMagnitudeWord)
open TransferBlstArmInverseSignedTopOperand01 (sourceFactorProductTopOffset)
open TransferBlstArmInverseSignedWordPrepare01 (sourceMaskPreparedWords)
open TransferBlstArmInverseWordMultiplyOffset01 (sourceOffsetWordMultiply)
open TransferBlstArmInverseSignedWordMultiply01 (sourceSignedMagnitudeProductWords)
open TransferBlstArmInverseSignedProductSum01 (sourceSignedProductSum)
open TransferBlstArmInverseWordSum01 (sourceWordSum)
open TransferBlstArmInverseExtrChain01 (sourceExtractChain)
open TransferBlstArmInversePackedInputRow01 (sourceFactorRowCodes sourceOriginalInputFactorWords)
open TransferBlstArmInverseOriginalRowWords01 (sourceOriginalFactorRow sourceOriginalRowWordSum)
open TransferBlstArmInverseOriginalRowMagnitude01 (sourceOriginalRowMagnitudeWords sourceOriginalRowQuotient)
open TransferBlstArmInverseWordMagnitudeBatch01 (sourceMagnitudeWordBatch)
open TransferBlstArmInverseWordRepack01 (sourceFourWordsOfNat)
open TransferBlstArmInverseMagnitudeBatch01 (sourceMagnitudeBatch)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords)
attribute [local irreducible] sourceSignedWordCode sourceFactorSignMask sourceFactorMagnitudeWord
  sourceFactorProductTopOffset sourceMaskPreparedWords sourceOffsetWordMultiply sourceWordSum
  sourceExtractChain sourceSignedMagnitudeProductWords sourceSignedProductSum sourceFactorRowCodes
  sourceOriginalInputFactorWords sourceOriginalFactorRow sourceOriginalRowWordSum sourceOriginalRowMagnitudeWords
  sourceOriginalRowQuotient sourceFourWordsOfNat sourceMagnitudeWordBatch sourceMagnitudeBatch

/-! Source word products now consume the factor registers produced by the
original input window, modulo64 packed recurrence and UBFX/bias subtraction.
Entire carry/EXTR31/sign/absolute outputs coincide with the proved source
magnitude batch. Actual UInt64 loop control, accumulated coefficient words,
private input producers, memory/ABI and compiled ISA remain separate. -/

def sourceWordFactorProduct (words : List UInt64) (factor : UInt64) : List UInt64 × Bool :=
  sourceOffsetWordMultiply (sourceMaskPreparedWords words (sourceFactorSignMask factor)).1
    (sourceFactorMagnitudeWord factor) (sourceFactorProductTopOffset factor)

theorem the_word_factor_program_at_an_exact_code_is_the_entire_signed_factor_program
    (words : List UInt64) (factor : Int) :
    sourceWordFactorProduct words (sourceSignedWordCode factor) = sourceSignedMagnitudeProductWords words factor := by
  unfold sourceWordFactorProduct sourceSignedMagnitudeProductWords
  rfl

def sourceWordFactorRowSum (left right : List UInt64) (factors : UInt64 × UInt64) : List UInt64 × Bool :=
  sourceWordSum (sourceWordFactorProduct left factors.1).1 (sourceWordFactorProduct right factors.2).1

theorem exact_factor_row_codes_derive_the_entire_two_product_word_sum_program
    (left right : List UInt64) (row : Int × Int) :
    sourceWordFactorRowSum left right (sourceFactorRowCodes row) = sourceSignedProductSum left right row.1 row.2 := by
  unfold sourceWordFactorRowSum sourceFactorRowCodes sourceSignedProductSum
  rw [the_word_factor_program_at_an_exact_code_is_the_entire_signed_factor_program,
    the_word_factor_program_at_an_exact_code_is_the_entire_signed_factor_program]

attribute [local irreducible] sourceWordFactorProduct sourceWordFactorRowSum

def sourcePackedRowWordSum (second : Bool) (a b : SourceFourWords) : List UInt64 × Bool :=
  sourceWordFactorRowSum [a.w0, a.w1, a.w2, a.w3] [b.w0, b.w1, b.w2, b.w3]
    (sourceOriginalInputFactorWords second a b)

theorem original_packed_factor_words_feed_the_entire_original_signed_row_word_sum
    (second : Bool) (a b : SourceFourWords) :
    sourcePackedRowWordSum second a b = sourceOriginalRowWordSum second a b := by
  unfold sourcePackedRowWordSum
  rw [TransferBlstArmInversePackedInputRow01.original_input_window_packed_registers_and_slot_decoders_produce_both_entire_factor_row_codes,
    exact_factor_row_codes_derive_the_entire_two_product_word_sum_program]
  unfold sourceOriginalRowWordSum
  rfl

attribute [local irreducible] sourcePackedRowWordSum

def sourcePackedRowMagnitudeWords (second : Bool) (a b : SourceFourWords) : List UInt64 × Bool :=
  let shifted := sourceExtractChain 31 (sourcePackedRowWordSum second a b).1
  sourceMaskPreparedWords shifted.1 (sourceFactorSignMask shifted.2)

theorem original_packed_factor_word_program_derives_the_entire_qualified_source_row_magnitude_program
    (second : Bool) (a b : SourceFourWords) :
    sourcePackedRowMagnitudeWords second a b = sourceOriginalRowMagnitudeWords second a b := by
  unfold sourcePackedRowMagnitudeWords sourceOriginalRowMagnitudeWords
  simp only [original_packed_factor_words_feed_the_entire_original_signed_row_word_sum]

attribute [local irreducible] sourcePackedRowMagnitudeWords

theorem original_packed_factor_products_carries_extr_and_sign_correction_derive_the_entire_original_quotient_magnitude
    (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    packWords (sourcePackedRowMagnitudeWords second a b).1 = (sourceOriginalRowQuotient 31 second a b).natAbs := by
  rw [original_packed_factor_word_program_derives_the_entire_qualified_source_row_magnitude_program]
  exact TransferBlstArmInverseOriginalRowMagnitude01.original_source_signed_products_carry_extr_asr_and_absolute_correction_derive_the_entire_quotient_magnitude second a b oddB

theorem two_symbolic_output_functions_equal_at_every_row_derive_the_entire_pair
    (left right : Bool → List UInt64) (rows : ∀ second, left second = right second) :
    (left false, left true) = (right false, right true) := by
  exact Prod.ext (rows false) (rows true)

def sourcePackedMagnitudeWordBatch (input : Nat × Nat) : List UInt64 × List UInt64 :=
  let a := sourceFourWordsOfNat input.1
  let b := sourceFourWordsOfNat input.2
  ((sourcePackedRowMagnitudeWords false a b).1, (sourcePackedRowMagnitudeWords true a b).1)

theorem original_packed_register_word_programs_derive_both_entire_source_word_batch_outputs
    (input : Nat × Nat) : sourcePackedMagnitudeWordBatch input = sourceMagnitudeWordBatch input := by
  let a := sourceFourWordsOfNat input.1
  let b := sourceFourWordsOfNat input.2
  have complete := two_symbolic_output_functions_equal_at_every_row_derive_the_entire_pair
    (fun second => (sourcePackedRowMagnitudeWords second a b).1)
    (fun second => (sourceOriginalRowMagnitudeWords second a b).1)
    (fun second => congrArg Prod.fst
      (original_packed_factor_word_program_derives_the_entire_qualified_source_row_magnitude_program second a b))
  unfold sourcePackedMagnitudeWordBatch sourceMagnitudeWordBatch
  exact complete

theorem original_packed_register_products_carries_shifts_and_signs_derive_both_entire_magnitude_batch_values
    (input : Nat × Nat) (odd : input.2 % 2 = 1) :
    (packWords (sourcePackedMagnitudeWordBatch input).1, packWords (sourcePackedMagnitudeWordBatch input).2) = sourceMagnitudeBatch input := by
  have words := original_packed_register_word_programs_derive_both_entire_source_word_batch_outputs input
  have packed := congrArg (fun output : List UInt64 × List UInt64 => (packWords output.1, packWords output.2)) words
  exact packed.trans
    (TransferBlstArmInverseWordMagnitudeBatch01.original_repacked_signed_word_operations_derive_both_complete_magnitude_batch_outputs input odd)

set_option pp.all true in
#check @sourceWordFactorProduct
#print axioms sourceWordFactorProduct
set_option pp.all true in
#check @the_word_factor_program_at_an_exact_code_is_the_entire_signed_factor_program
#print axioms the_word_factor_program_at_an_exact_code_is_the_entire_signed_factor_program
set_option pp.all true in
#check @sourceWordFactorRowSum
#print axioms sourceWordFactorRowSum
set_option pp.all true in
#check @exact_factor_row_codes_derive_the_entire_two_product_word_sum_program
#print axioms exact_factor_row_codes_derive_the_entire_two_product_word_sum_program
set_option pp.all true in
#check @sourcePackedRowWordSum
#print axioms sourcePackedRowWordSum
set_option pp.all true in
#check @original_packed_factor_words_feed_the_entire_original_signed_row_word_sum
#print axioms original_packed_factor_words_feed_the_entire_original_signed_row_word_sum
set_option pp.all true in
#check @sourcePackedRowMagnitudeWords
#print axioms sourcePackedRowMagnitudeWords
set_option pp.all true in
#check @original_packed_factor_word_program_derives_the_entire_qualified_source_row_magnitude_program
#print axioms original_packed_factor_word_program_derives_the_entire_qualified_source_row_magnitude_program
set_option pp.all true in
#check @original_packed_factor_products_carries_extr_and_sign_correction_derive_the_entire_original_quotient_magnitude
#print axioms original_packed_factor_products_carries_extr_and_sign_correction_derive_the_entire_original_quotient_magnitude
set_option pp.all true in
#check @two_symbolic_output_functions_equal_at_every_row_derive_the_entire_pair
#print axioms two_symbolic_output_functions_equal_at_every_row_derive_the_entire_pair
set_option pp.all true in
#check @sourcePackedMagnitudeWordBatch
#print axioms sourcePackedMagnitudeWordBatch
set_option pp.all true in
#check @original_packed_register_word_programs_derive_both_entire_source_word_batch_outputs
#print axioms original_packed_register_word_programs_derive_both_entire_source_word_batch_outputs
set_option pp.all true in
#check @original_packed_register_products_carries_shifts_and_signs_derive_both_entire_magnitude_batch_values
#print axioms original_packed_register_products_carries_shifts_and_signs_derive_both_entire_magnitude_batch_values
end ShielddSecurity.TransferBlstArmInversePackedRowProgram01
