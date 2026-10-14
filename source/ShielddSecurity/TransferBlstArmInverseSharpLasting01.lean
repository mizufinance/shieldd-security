import ShielddSecurity.TransferBlstArmInverseRowTransition01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSharpLasting01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseFirstMismatch01 (sourceFirstControlMismatch)
open TransferBlstArmInverseFullWidth01 (sourceClippedJointBitwidth)

/-! UNRUN sharp lasting signed bounds for original rows. Exact both-row
transitions and original prefix errors preserve one component inside one
error budget through prefix31. Maximum magnitude never increases from any
earlier prefix. Total pair bitlength decrease and native operations stay open. -/

theorem original_first_mismatch_keeps_one_signed_component_within_one_error_budget_through31
    (count remaining : Nat) (a b : SourceFourWords) (bounded : count < 31)
    (lastBound : count + 1 + remaining ≤ 31) (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approxA := sourceApproxLow31 windows.1 a.w0
    let approxB := sourceApproxLow31 windows.2 b.w0
    let approximate := sourceFactorInitial approxA approxB
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    let signed := sourceActualFactorQuotients (count + 1 + remaining) approxA approxB
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    sourceFirstControlMismatch count approximate actual →
      min signed.1.natAbs signed.2.natAbs ≤ 2 ^ sourceFourWordWindowShift a b * 2147483648 := by
  dsimp only
  revert lastBound
  induction remaining with
  | zero =>
      intro lastBound first
      have small := TransferBlstArmInverseNextRow01.original_first_mismatch_next_controlled_quotient_has_the_derived_half_gap_bound
        count a b bounded oddB first
      have constant : (2 : Nat) ^ 31 = 2147483648 := by decide +kernel
      rw [Nat.pow_add, constant] at small
      exact Nat.le_trans (Nat.min_le_left _ _) small
  | succ remaining ih =>
      intro lastBound first
      have previous := ih (by omega) first
      have errors := TransferBlstArmInverseWindowError01.original_source_produced_four_word_windows_derive_both_factor_prefix_error_bounds
        (count + 1 + remaining) a b (by omega) oddB
      have step := TransferBlstArmInverseSignedStep01.original_signed_control_step_preserves_a_component_within_one_error_budget
        _ _ _ _ (2 ^ sourceFourWordWindowShift a b) (2 ^ sourceFourWordWindowShift a b * 2147483648)
        previous errors.1 errors.2
      have transition := TransferBlstArmInverseRowTransition01.original_four_word_factor_quotients_follow_the_exact_signed_control_step
        (count + 1 + remaining) a b (by omega) oddB
      rw [←transition] at step
      have index : count + 1 + (remaining + 1) = (count + 1 + remaining) + 1 := by omega
      rw [index]
      exact step

theorem original_signed_quotient_maximum_never_increases_from_any_earlier_prefix_through31
    (count remaining : Nat) (a b : SourceFourWords)
    (bounded : count + remaining ≤ 31) (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approxA := sourceApproxLow31 windows.1 a.w0
    let approxB := sourceApproxLow31 windows.2 b.w0
    let before := sourceActualFactorQuotients count approxA approxB
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    let after := sourceActualFactorQuotients (count + remaining) approxA approxB
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    max after.1.natAbs after.2.natAbs ≤ max before.1.natAbs before.2.natAbs := by
  dsimp only
  revert bounded
  induction remaining with
  | zero => intro bounded; exact Nat.le_refl _
  | succ remaining ih =>
      intro bounded
      let approxA := sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0
      let approxB := sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0
      let current := sourceActualFactorQuotients (count + remaining) approxA approxB
        (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
      let factors := sourceFactorWalk (count + remaining) (sourceFactorInitial approxA approxB)
      have previous := ih (by omega)
      have one := TransferBlstArmInverseSignedStep01.every_signed_control_step_does_not_increase_the_larger_magnitude
        current.1 current.2 factors.a factors.b
      have transition := TransferBlstArmInverseRowTransition01.original_four_word_factor_quotients_follow_the_exact_signed_control_step
        (count + remaining) a b (by omega) oddB
      rw [←transition] at one
      have index : count + (remaining + 1) = (count + remaining) + 1 := by omega
      rw [index]
      exact Nat.le_trans one previous

theorem original_first_mismatch_final_small_component_is_bounded_at_full_width_minus33
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31)
    (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approxA := sourceApproxLow31 windows.1 a.w0
    let approxB := sourceApproxLow31 windows.2 b.w0
    let approximate := sourceFactorInitial approxA approxB
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    let final := sourceActualFactorQuotients 31 approxA approxB
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    sourceFirstControlMismatch count approximate actual →
      min final.1.natAbs final.2.natAbs ≤ 2 ^ (sourceClippedJointBitwidth a b - 33) := by
  dsimp only
  intro first
  have sum : count + 1 + (31 - (count + 1)) = 31 := by omega
  have lasting := original_first_mismatch_keeps_one_signed_component_within_one_error_budget_through31
    count (31 - (count + 1)) a b bounded (by omega) oddB first
  rw [sum] at lasting
  have width := TransferBlstArmInverseFullWidth01.original_computed_shift_plus64_is_the_exact_clipped_full_input_joint_bitwidth a b
  have exponent : sourceClippedJointBitwidth a b - 33 = sourceFourWordWindowShift a b + 31 := by omega
  have constant : (2 : Nat) ^ 31 = 2147483648 := by decide +kernel
  simpa only [exponent, Nat.pow_add, constant] using lasting

set_option pp.all true in
#check @original_first_mismatch_keeps_one_signed_component_within_one_error_budget_through31
#print axioms original_first_mismatch_keeps_one_signed_component_within_one_error_budget_through31
set_option pp.all true in
#check @original_signed_quotient_maximum_never_increases_from_any_earlier_prefix_through31
#print axioms original_signed_quotient_maximum_never_increases_from_any_earlier_prefix_through31
set_option pp.all true in
#check @original_first_mismatch_final_small_component_is_bounded_at_full_width_minus33
#print axioms original_first_mismatch_final_small_component_is_bounded_at_full_width_minus33
end ShielddSecurity.TransferBlstArmInverseSharpLasting01
