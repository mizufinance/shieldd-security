import ShielddSecurity.TransferBlstArmInverseBatchProgress01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowBatchOdd01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseSignedStep01 (sourceSignedControlStep)
attribute [local irreducible] sourceFactorWalk sourceActualFactorQuotients

/-! Exact original batch second-output oddness. The last transition uses
prefix30 parity and the original signed step; no unsupported prefix31
parity observation is assumed. Native arithmetic remains separate. -/

theorem matched_control_parity_and_odd_second_input_preserve_signed_second_oddness
    (x y : Int) (p q : Nat) (odd : y % 2 = 1) (matched : x % 2 = (p : Int) % 2) :
    (sourceSignedControlStep p q x y).2 % 2 = 1 := by
  unfold sourceSignedControlStep
  by_cases even : p % 2 = 0
  · rw [if_pos even]
    exact odd
  · rw [if_neg even]
    by_cases order : q ≤ p
    · rw [if_pos order]
      exact odd
    · rw [if_neg order]
      have pOdd : p % 2 = 1 := by omega
      change x % 2 = 1
      omega

theorem every_valid_symbolic_prefix_step_retains_an_odd_signed_second_output
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1) :
    (sourceActualFactorQuotients (count + 1)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)).2 % 2 = 1 := by
  let approxA := sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0
  let approxB := sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0
  let factors := sourceFactorWalk count (sourceFactorInitial approxA approxB)
  let actual := sourceActualFactorQuotients count approxA approxB
    (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
  have parity := TransferBlstArmInversePrefixParity01.original_four_word_inputs_derive_both_signed_prefix_quotient_parities
    count (sourceFourWordWindowWords a b).1 (sourceFourWordWindowWords a b).2 a b bounded oddB
  change actual.1 % 2 = (factors.a : Int) % 2 ∧ actual.2 % 2 = (factors.b : Int) % 2 at parity
  have approxOdd := TransferBlstArmInverseApproxBits01.original_low31_approximation_preserves_oddness_of_the_original_low_word
    (sourceFourWordWindowWords a b).2 b.w0 oddB
  have naturalOdd := TransferBlstArmInverseNaturalScale01.every_original_natural_factor_walk_retains_its_odd_second_input
    count (sourceFactorInitial approxA approxB) approxOdd
  change factors.b % 2 = 1 at naturalOdd
  have actualOdd : actual.2 % 2 = 1 := by omega
  have next := matched_control_parity_and_odd_second_input_preserve_signed_second_oddness
    actual.1 actual.2 factors.a factors.b actualOdd parity.1
  have transition := TransferBlstArmInverseRowTransition01.original_four_word_factor_quotients_follow_the_exact_signed_control_step
    count a b (Nat.le_of_lt bounded) oddB
  dsimp only [actual, factors, approxA, approxB] at next
  dsimp only at transition
  rw [←transition] at next
  exact next

theorem original_four_word31_step_batch_retains_an_odd_signed_second_output
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    (sourceActualFactorQuotients 31
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)).2 % 2 = 1 := by
  exact every_valid_symbolic_prefix_step_retains_an_odd_signed_second_output 30 a b (by decide) oddB

theorem a_signed_odd_value_has_an_odd_natural_magnitude
    (value : Int) (odd : value % 2 = 1) : value.natAbs % 2 = 1 := by
  by_cases nonnegative : 0 ≤ value
  · have absolute := Int.eq_natAbs_of_nonneg nonnegative
    omega
  · have absolute := Int.eq_neg_natAbs_of_nonpos (show value ≤ 0 by omega)
    omega

theorem original_four_word31_step_batch_retains_an_odd_second_magnitude
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    (sourceActualFactorQuotients 31
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)).2.natAbs % 2 = 1 := by
  exact a_signed_odd_value_has_an_odd_natural_magnitude _
    (original_four_word31_step_batch_retains_an_odd_signed_second_output a b oddB)

set_option pp.all true in
#check @matched_control_parity_and_odd_second_input_preserve_signed_second_oddness
#print axioms matched_control_parity_and_odd_second_input_preserve_signed_second_oddness
set_option pp.all true in
#check @every_valid_symbolic_prefix_step_retains_an_odd_signed_second_output
#print axioms every_valid_symbolic_prefix_step_retains_an_odd_signed_second_output
set_option pp.all true in
#check @original_four_word31_step_batch_retains_an_odd_signed_second_output
#print axioms original_four_word31_step_batch_retains_an_odd_signed_second_output
set_option pp.all true in
#check @a_signed_odd_value_has_an_odd_natural_magnitude
#print axioms a_signed_odd_value_has_an_odd_natural_magnitude
set_option pp.all true in
#check @original_four_word31_step_batch_retains_an_odd_second_magnitude
#print axioms original_four_word31_step_batch_retains_an_odd_second_magnitude
end ShielddSecurity.TransferBlstArmInverseWindowBatchOdd01
