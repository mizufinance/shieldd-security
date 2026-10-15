import ShielddSecurity.TransferBlstArmInverseWordLoopCounter01
import ShielddSecurity.TransferBlstArmInversePackedInputRow01
import ShielddSecurity.TransferBlstArmInverseWindowReturned01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordLoopFactorWords01
open TransferBlstArmInverseWordPackedStep01 (WordPackedState sourcePackedWordCode)
open TransferBlstArmInverseWordPackedWalk01 (sourceWordPackedInitial)
open TransferBlstArmInverseWordLoopCounter01 (sourceCountedWordPackedRun)
open TransferBlstArmInversePackedFactorWords01 (sourcePackedFactorRegisterWords)
open TransferBlstArmInverseDebiasWord01 (sourceLowFactorWord sourceHighFactorWord)
open TransferBlstArmInversePackedWalk01 (PackedState sourcePackedWalk sourcePackedInitial)
open TransferBlstArmInverseFactors01 (sourceFactorWalk sourceFactorInitial)
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords)
open TransferBlstArmInverseWindowReturned01 (sourceFourWordApproximationWords)
open TransferBlstArmInversePackedInputRow01 (sourceInputPackedFactorRegisters sourceSelectFactorWordRow sourceOriginalInputFactorWords)
attribute [local irreducible] sourceCountedWordPackedRun sourceWordPackedInitial
  sourcePackedWordCode sourcePackedWalk sourcePackedInitial sourceFactorWalk
  sourcePackedFactorRegisterWords sourceFourWordApproximationWords sourceInputPackedFactorRegisters
  sourceSelectFactorWordRow sourceOriginalInputFactorWords

/-! The source UInt64 counter loop supplies the actual words consumed by
the UBFX/bias decoders. Original four-word approximation producers then
supply both complete row factors. Compiled execution and ABI remain open. -/

def sourceWordStateFactorWords (words : WordPackedState) : UInt64 × UInt64 × UInt64 × UInt64 :=
  (sourceLowFactorWord words.2.2.1, sourceHighFactorWord words.2.2.1,
   sourceLowFactorWord words.2.2.2, sourceHighFactorWord words.2.2.2)

theorem decoding_the_entire_packed_state_code_preserves_all_four_factor_words
    (state : PackedState) : sourceWordStateFactorWords (sourcePackedWordCode state) =
      sourcePackedFactorRegisterWords state := by
  unfold sourceWordStateFactorWords sourcePackedWordCode sourcePackedFactorRegisterWords
  rfl

attribute [local irreducible] sourceWordStateFactorWords

def sourceCountedLoopFactorWords (a b : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  sourceWordStateFactorWords (sourceCountedWordPackedRun 31 (31, sourceWordPackedInitial a b)).2

theorem original_counted_word_loop_and_slot_decoders_equal_the_entire_original_packed_factor_words
    (a b : UInt64) : sourceCountedLoopFactorWords a b =
      sourcePackedFactorRegisterWords (sourcePackedWalk 31 (sourcePackedInitial a.toNat b.toNat)) := by
  unfold sourceCountedLoopFactorWords
  rw [TransferBlstArmInverseWordLoopCounter01.original31_counted_word_loop_with_original_constants_produces_the_entire_original_packed_state_code]
  exact decoding_the_entire_packed_state_code_preserves_all_four_factor_words _

attribute [local irreducible] sourceCountedLoopFactorWords

theorem original_counted_word_loop_derives_all_four_entire_integer_factor_codes
    (a b : UInt64) : sourceCountedLoopFactorWords a b =
      (sourceSignedWordCode (sourceFactorWalk 31 (sourceFactorInitial a.toNat b.toNat)).f0,
       sourceSignedWordCode (sourceFactorWalk 31 (sourceFactorInitial a.toNat b.toNat)).g0,
       sourceSignedWordCode (sourceFactorWalk 31 (sourceFactorInitial a.toNat b.toNat)).f1,
       sourceSignedWordCode (sourceFactorWalk 31 (sourceFactorInitial a.toNat b.toNat)).g1) := by
  rw [original_counted_word_loop_and_slot_decoders_equal_the_entire_original_packed_factor_words]
  exact TransferBlstArmInversePackedFactorWords01.original_modulo64_packed_walk_and_ubfx_bias_subtraction_derive_all_four_entire_factor_codes _ _

def sourceCountedInputFactorWords (a b : SourceFourWords) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let approximation := sourceFourWordApproximationWords a b
  sourceCountedLoopFactorWords approximation.1 approximation.2

theorem original_four_word_approximation_and_counted_loop_produce_all_four_existing_input_factor_words
    (a b : SourceFourWords) : sourceCountedInputFactorWords a b = sourceInputPackedFactorRegisters a b := by
  have observations := TransferBlstArmInverseWindowReturned01.original_returned_approximation_words_have_the_existing_model_observations a b
  unfold sourceCountedInputFactorWords
  rw [original_counted_word_loop_and_slot_decoders_equal_the_entire_original_packed_factor_words,
    observations.1, observations.2]
  unfold sourceInputPackedFactorRegisters
  rfl

attribute [local irreducible] sourceCountedInputFactorWords

theorem selecting_either_counted_source_loop_row_produces_both_entire_existing_factor_words
    (second : Bool) (a b : SourceFourWords) :
    sourceSelectFactorWordRow second (sourceCountedInputFactorWords a b) =
      sourceOriginalInputFactorWords second a b := by
  rw [original_four_word_approximation_and_counted_loop_produce_all_four_existing_input_factor_words]
  unfold sourceOriginalInputFactorWords
  rfl

set_option pp.all true in
#check @sourceWordStateFactorWords
#print axioms sourceWordStateFactorWords
set_option pp.all true in
#check @decoding_the_entire_packed_state_code_preserves_all_four_factor_words
#print axioms decoding_the_entire_packed_state_code_preserves_all_four_factor_words
set_option pp.all true in
#check @sourceCountedLoopFactorWords
#print axioms sourceCountedLoopFactorWords
set_option pp.all true in
#check @original_counted_word_loop_and_slot_decoders_equal_the_entire_original_packed_factor_words
#print axioms original_counted_word_loop_and_slot_decoders_equal_the_entire_original_packed_factor_words
set_option pp.all true in
#check @original_counted_word_loop_derives_all_four_entire_integer_factor_codes
#print axioms original_counted_word_loop_derives_all_four_entire_integer_factor_codes
set_option pp.all true in
#check @sourceCountedInputFactorWords
#print axioms sourceCountedInputFactorWords
set_option pp.all true in
#check @original_four_word_approximation_and_counted_loop_produce_all_four_existing_input_factor_words
#print axioms original_four_word_approximation_and_counted_loop_produce_all_four_existing_input_factor_words
set_option pp.all true in
#check @selecting_either_counted_source_loop_row_produces_both_entire_existing_factor_words
#print axioms selecting_either_counted_source_loop_row_produces_both_entire_existing_factor_words
end ShielddSecurity.TransferBlstArmInverseWordLoopFactorWords01
