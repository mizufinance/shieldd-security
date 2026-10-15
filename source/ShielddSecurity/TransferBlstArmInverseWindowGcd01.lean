import ShielddSecurity.TransferBlstArmInverseMagnitudeBatch01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowGcd01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseWordRepack01 (sourceFourWordsOfNat)
open TransferBlstArmInverseMagnitudeBatch01 (sourceMagnitudeBatch)
attribute [local irreducible] sourceFactorWalk sourceActualFactorQuotients

/-! Entire GCD preservation for the original window-produced source batch.
Original low31 lifts derive the signed parity at each valid prefix; exact
signed transitions and symbolic induction preserve GCD through31. The
magnitude/repacking model follows under exact input capacity. Native
instruction correspondence and inverse-unit conclusions remain open. -/

theorem every_valid_original_window_prefix_step_preserves_the_full_signed_gcd
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1) :
    let approxA := sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0
    let approxB := sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0
    let before := sourceActualFactorQuotients count approxA approxB (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    let after := sourceActualFactorQuotients (count + 1) approxA approxB (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    Int.gcd after.1 after.2 = Int.gcd before.1 before.2 := by
  dsimp only
  let approxA := sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0
  let approxB := sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0
  let factors := sourceFactorWalk count (sourceFactorInitial approxA approxB)
  let actual := sourceActualFactorQuotients count approxA approxB
    (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
  have parity := TransferBlstArmInversePrefixParity01.original_four_word_inputs_derive_both_signed_prefix_quotient_parities
    count (sourceFourWordWindowWords a b).1 (sourceFourWordWindowWords a b).2 a b bounded oddB
  change actual.1 % 2 = (factors.a : Int) % 2 ∧ actual.2 % 2 = (factors.b : Int) % 2 at parity
  have approximateOdd := TransferBlstArmInverseApproxBits01.original_low31_approximation_preserves_oddness_of_the_original_low_word
    (sourceFourWordWindowWords a b).2 b.w0 oddB
  have naturalOdd := TransferBlstArmInverseNaturalScale01.every_original_natural_factor_walk_retains_its_odd_second_input
    count (sourceFactorInitial approxA approxB) approximateOdd
  change factors.b % 2 = 1 at naturalOdd
  have actualOdd : actual.2 % 2 = 1 := by omega
  have step := TransferBlstArmInverseControlledGcd01.matched_parity_and_odd_second_value_make_the_original_signed_control_step_preserve_gcd
    actual.1 actual.2 factors.a factors.b actualOdd parity.1
  have transition := TransferBlstArmInverseRowTransition01.original_four_word_factor_quotients_follow_the_exact_signed_control_step
    count a b (Nat.le_of_lt bounded) oddB
  dsimp only [actual, factors, approxA, approxB] at step
  dsimp only at transition
  rw [←transition] at step
  exact step

theorem every_original_window_prefix_through31_preserves_the_entire_input_gcd
    (count : Nat) (a b : SourceFourWords) (bounded : count ≤ 31) (oddB : b.w0.toNat % 2 = 1) :
    let actual := sourceActualFactorQuotients count
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    Int.gcd actual.1 actual.2 = Int.gcd (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int) := by
  dsimp only
  revert bounded
  induction count with
  | zero =>
    intro bounded
    rw [TransferBlstArmInverseBatchRange01.initialized_zero_prefix_full_quotients_are_the_original_inputs]
  | succ count ih =>
    intro bounded
    have previous := ih (by omega)
    have step := every_valid_original_window_prefix_step_preserves_the_full_signed_gcd count a b (by omega) oddB
    exact step.trans previous

theorem every_original_bounded_window_prefix_preserves_the_gcd_of_the_full_output_magnitudes
    (count : Nat) (a b : SourceFourWords) (bounded : count ≤ 31) (oddB : b.w0.toNat % 2 = 1) :
    let actual := sourceActualFactorQuotients count
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    Nat.gcd actual.1.natAbs actual.2.natAbs = Nat.gcd (sourcePackedFourWords a) (sourcePackedFourWords b) := by
  dsimp only
  change Int.gcd
    (sourceActualFactorQuotients count
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)).1
    (sourceActualFactorQuotients count
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)).2 =
    Int.gcd (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
  exact every_original_window_prefix_through31_preserves_the_entire_input_gcd count a b bounded oddB

theorem every_original31_step_window_batch_preserves_the_gcd_of_the_full_output_magnitudes
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    let actual := sourceActualFactorQuotients 31
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    Nat.gcd actual.1.natAbs actual.2.natAbs = Nat.gcd (sourcePackedFourWords a) (sourcePackedFourWords b) := by
  exact every_original_bounded_window_prefix_preserves_the_gcd_of_the_full_output_magnitudes 31 a b (Nat.le_refl _) oddB

theorem every_valid_source_magnitude_batch_preserves_the_entire_input_gcd
    (input : Nat × Nat) (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256)
    (odd : input.2 % 2 = 1) :
    Nat.gcd (sourceMagnitudeBatch input).1 (sourceMagnitudeBatch input).2 = Nat.gcd input.1 input.2 := by
  have previous := every_original31_step_window_batch_preserves_the_gcd_of_the_full_output_magnitudes
    (sourceFourWordsOfNat input.1) (sourceFourWordsOfNat input.2)
    (TransferBlstArmInverseWordRepack01.an_odd_natural_input_has_an_odd_original_repacked_low_word input.2 odd)
  have left := TransferBlstArmInverseWordRepack01.original_four_word_repacking_reconstructs_every_input_below_two256 input.1 leftBound
  have right := TransferBlstArmInverseWordRepack01.original_four_word_repacking_reconstructs_every_input_below_two256 input.2 rightBound
  dsimp only at previous
  dsimp only [sourceMagnitudeBatch]
  rw [left, right] at previous ⊢
  exact previous

set_option pp.all true in
#check @every_valid_original_window_prefix_step_preserves_the_full_signed_gcd
#print axioms every_valid_original_window_prefix_step_preserves_the_full_signed_gcd
set_option pp.all true in
#check @every_original_window_prefix_through31_preserves_the_entire_input_gcd
#print axioms every_original_window_prefix_through31_preserves_the_entire_input_gcd
set_option pp.all true in
#check @every_original_bounded_window_prefix_preserves_the_gcd_of_the_full_output_magnitudes
#print axioms every_original_bounded_window_prefix_preserves_the_gcd_of_the_full_output_magnitudes
set_option pp.all true in
#check @every_original31_step_window_batch_preserves_the_gcd_of_the_full_output_magnitudes
#print axioms every_original31_step_window_batch_preserves_the_gcd_of_the_full_output_magnitudes
set_option pp.all true in
#check @every_valid_source_magnitude_batch_preserves_the_entire_input_gcd
#print axioms every_valid_source_magnitude_batch_preserves_the_entire_input_gcd
end ShielddSecurity.TransferBlstArmInverseWindowGcd01
