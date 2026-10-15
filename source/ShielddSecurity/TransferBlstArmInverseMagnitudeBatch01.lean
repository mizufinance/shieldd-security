import ShielddSecurity.TransferBlstArmInverseControlledGcd01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseMagnitudeBatch01
open TransferBlstArmInverseWordRepack01 (sourceFourWordsOfNat)
open TransferBlstArmInverseWindowSelect01 (sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseBitlengthBudget01 (sourceNatBitlength)

/-! One complete source magnitude batch: exact word repacking, original
window producer, original factor rows, exact full quotients and magnitudes.
Capacity, oddness, zero stability and conditional pair progress derive from
the original source lemmas. Compiled native execution remains open. -/

def sourceMagnitudeBatch (input : Nat × Nat) : Nat × Nat :=
  let a := sourceFourWordsOfNat input.1
  let b := sourceFourWordsOfNat input.2
  let signed := sourceActualFactorQuotients 31
    (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
    (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
    (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
  (signed.1.natAbs, signed.2.natAbs)

theorem every_source_magnitude_batch_with_odd_second_input_returns_an_odd_second_magnitude
    (input : Nat × Nat) (odd : input.2 % 2 = 1) :
    (sourceMagnitudeBatch input).2 % 2 = 1 := by
  dsimp only [sourceMagnitudeBatch]
  exact TransferBlstArmInverseWindowBatchOdd01.original_four_word31_step_batch_retains_an_odd_second_magnitude
    (sourceFourWordsOfNat input.1) (sourceFourWordsOfNat input.2)
    (TransferBlstArmInverseWordRepack01.an_odd_natural_input_has_an_odd_original_repacked_low_word input.2 odd)

theorem every_source_magnitude_batch_with_odd_second_input_returns_two_values_that_fit_four_words
    (input : Nat × Nat) (odd : input.2 % 2 = 1) :
    (sourceMagnitudeBatch input).1 < 2 ^ 256 ∧ (sourceMagnitudeBatch input).2 < 2 ^ 256 := by
  dsimp only [sourceMagnitudeBatch]
  exact TransferBlstArmInverseBatchRange01.every_original31_step_full_output_magnitude_fits_four_words
    (sourceFourWordsOfNat input.1) (sourceFourWordsOfNat input.2)
    (TransferBlstArmInverseWordRepack01.an_odd_natural_input_has_an_odd_original_repacked_low_word input.2 odd)

theorem every_source_magnitude_batch_keeps_a_zero_first_input_zero
    (input : Nat × Nat) (zero : input.1 = 0) : (sourceMagnitudeBatch input).1 = 0 := by
  have zeroPacked : sourcePackedFourWords (sourceFourWordsOfNat input.1) = 0 := by
    rw [zero]
    exact TransferBlstArmInverseWordRepack01.original_four_word_repacking_reconstructs_every_input_below_two256 0 (Nat.two_pow_pos _)
  have terminal := TransferBlstArmInverseBatchZero01.an_original_zero_first_full_input_stays_zero_after_the31_step_source_batch
    (sourceFourWordsOfNat input.1) (sourceFourWordsOfNat input.2) zeroPacked
  dsimp only [sourceMagnitudeBatch]
  rw [terminal]
  rfl

theorem every_valid_source_magnitude_batch_reaches_zero_or_decreases_total_pair_bitlength_by31
    (input : Nat × Nat) (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256)
    (odd : input.2 % 2 = 1) :
    (sourceMagnitudeBatch input).1 = 0 ∨
      sourceNatBitlength (sourceMagnitudeBatch input).1 + sourceNatBitlength (sourceMagnitudeBatch input).2 + 31 ≤
        sourceNatBitlength input.1 + sourceNatBitlength input.2 := by
  have progress := TransferBlstArmInverseBatchProgress01.every_original_four_word31_step_batch_reaches_zero_or_decreases_pair_bitlength_by31
    (sourceFourWordsOfNat input.1) (sourceFourWordsOfNat input.2)
    (TransferBlstArmInverseWordRepack01.an_odd_natural_input_has_an_odd_original_repacked_low_word input.2 odd)
  have left := TransferBlstArmInverseWordRepack01.original_four_word_repacking_reconstructs_every_input_below_two256 input.1 leftBound
  have right := TransferBlstArmInverseWordRepack01.original_four_word_repacking_reconstructs_every_input_below_two256 input.2 rightBound
  dsimp only at progress
  dsimp only [sourceMagnitudeBatch]
  rw [left, right] at progress ⊢
  rcases progress with terminal | decreases
  · left
    rw [terminal]
    rfl
  · right
    exact decreases

set_option pp.all true in
#check @sourceMagnitudeBatch
#print axioms sourceMagnitudeBatch
set_option pp.all true in
#check @every_source_magnitude_batch_with_odd_second_input_returns_an_odd_second_magnitude
#print axioms every_source_magnitude_batch_with_odd_second_input_returns_an_odd_second_magnitude
set_option pp.all true in
#check @every_source_magnitude_batch_with_odd_second_input_returns_two_values_that_fit_four_words
#print axioms every_source_magnitude_batch_with_odd_second_input_returns_two_values_that_fit_four_words
set_option pp.all true in
#check @every_source_magnitude_batch_keeps_a_zero_first_input_zero
#print axioms every_source_magnitude_batch_keeps_a_zero_first_input_zero
set_option pp.all true in
#check @every_valid_source_magnitude_batch_reaches_zero_or_decreases_total_pair_bitlength_by31
#print axioms every_valid_source_magnitude_batch_reaches_zero_or_decreases_total_pair_bitlength_by31
end ShielddSecurity.TransferBlstArmInverseMagnitudeBatch01
