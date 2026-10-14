import ShielddSecurity.TransferBlstArmInverseSignedStep01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseRowTransition01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorInitial sourceFactorStep sourceFactorWalk)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseSignedStep01 (sourceSignedControlStep)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)

/-! UNRUN exact signed quotient recurrence for original coefficient updates.
Both reconstructed current rows come from original low31 divisibility, not
chosen values. All three controls derive both next quotient coordinates.
Sharp lasting induction follows separately; compiled word execution and
total pair bitlength progress remain open. -/

theorem scaled_value_divided_by_the_next_power_is_its_exact_signed_half
    (count : Nat) (value : Int) :
    ((2 : Int) ^ count * value) / (2 : Int) ^ (count + 1) = value / 2 := by
  rw [Int.pow_succ]
  exact Int.mul_ediv_mul_of_pos _ _ (Int.pow_pos (by decide))

theorem doubled_tracked_row_divided_by_the_next_power_is_the_exact_signed_value
    (count : Nat) (f g inputA inputB value : Int)
    (row : (2 : Int) ^ count * value = f * inputA + g * inputB) :
    ((2 * f) * inputA + (2 * g) * inputB) / (2 : Int) ^ (count + 1) = value := by
  have numerator : (2 * f) * inputA + (2 * g) * inputB = 2 * ((2 : Int) ^ count * value) := by
    rw [row, Int.mul_add]
    simp only [Int.mul_assoc]
  rw [numerator, Int.mul_left_comm 2 ((2 : Int) ^ count), Int.pow_succ]
  rw [Int.mul_ediv_mul_of_pos _ _ (Int.pow_pos (by decide))]
  exact Int.mul_ediv_cancel_left _ (by decide : (2 : Int) ≠ 0)

theorem original_controlled_coefficients_derive_the_complete_signed_control_step
    (count : Nat) (s : SourceFactors) (inputA inputB x y : Int)
    (leftRow : (2 : Int) ^ count * x = s.f0 * inputA + s.g0 * inputB)
    (rightRow : (2 : Int) ^ count * y = s.f1 * inputA + s.g1 * inputB) :
    (((sourceFactorStep s).f0 * inputA + (sourceFactorStep s).g0 * inputB) / (2 : Int) ^ (count + 1),
     ((sourceFactorStep s).f1 * inputA + (sourceFactorStep s).g1 * inputB) / (2 : Int) ^ (count + 1)) =
      sourceSignedControlStep s.a s.b x y := by
  by_cases even : s.a % 2 = 0
  · simp only [sourceFactorStep, sourceSignedControlStep, if_pos even]
    apply Prod.ext
    · rw [←leftRow]
      exact scaled_value_divided_by_the_next_power_is_its_exact_signed_half _ _
    · exact doubled_tracked_row_divided_by_the_next_power_is_the_exact_signed_value _ _ _ _ _ _ rightRow
  · by_cases ordered : s.b ≤ s.a
    · simp only [sourceFactorStep, sourceSignedControlStep, if_neg even, if_pos ordered]
      apply Prod.ext
      · have first := TransferBlstArmInverseNextRow01.odd_source_step_first_row_is_the_oriented_signed_half_gap
          count s inputA inputB x y even leftRow rightRow
        simpa only [sourceFactorStep, if_neg even, if_pos ordered] using first
      · exact doubled_tracked_row_divided_by_the_next_power_is_the_exact_signed_value _ _ _ _ _ _ rightRow
    · simp only [sourceFactorStep, sourceSignedControlStep, if_neg even, if_neg ordered]
      apply Prod.ext
      · have first := TransferBlstArmInverseNextRow01.odd_source_step_first_row_is_the_oriented_signed_half_gap
          count s inputA inputB x y even leftRow rightRow
        simpa only [sourceFactorStep, if_neg even, if_neg ordered] using first
      · exact doubled_tracked_row_divided_by_the_next_power_is_the_exact_signed_value _ _ _ _ _ _ leftRow

theorem original_four_word_factor_quotients_follow_the_exact_signed_control_step
    (count : Nat) (a b : SourceFourWords) (bounded : count ≤ 31)
    (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approxA := sourceApproxLow31 windows.1 a.w0
    let approxB := sourceApproxLow31 windows.2 b.w0
    let factors := sourceFactorWalk count (sourceFactorInitial approxA approxB)
    let old := sourceActualFactorQuotients count approxA approxB
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    sourceActualFactorQuotients (count + 1) approxA approxB
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int) =
      sourceSignedControlStep factors.a factors.b old.1 old.2 := by
  dsimp only
  let approxA := sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0
  let approxB := sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0
  let factors := sourceFactorWalk count (sourceFactorInitial approxA approxB)
  let old := sourceActualFactorQuotients count approxA approxB
    (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
  have divisible := TransferBlstArmInversePrefixDiv01.original_initialized_factor_prefixes_divide_both_entire_input_rows
    count (sourceFourWordWindowWords a b).1 a.w0 (sourceFourWordWindowWords a b).2 b.w0
    [a.w1, a.w2, a.w3] [b.w1, b.w2, b.w3] bounded oddB
  have leftRow : (2 : Int) ^ count * old.1 =
      factors.f0 * (sourcePackedFourWords a : Int) + factors.g0 * (sourcePackedFourWords b : Int) :=
    Int.mul_ediv_cancel_of_dvd divisible.1
  have rightRow : (2 : Int) ^ count * old.2 =
      factors.f1 * (sourcePackedFourWords a : Int) + factors.g1 * (sourcePackedFourWords b : Int) :=
    Int.mul_ediv_cancel_of_dvd divisible.2
  have step := original_controlled_coefficients_derive_the_complete_signed_control_step count factors
    (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int) old.1 old.2 leftRow rightRow
  change (((sourceFactorWalk (count + 1) (sourceFactorInitial approxA approxB)).f0 * (sourcePackedFourWords a : Int) +
    (sourceFactorWalk (count + 1) (sourceFactorInitial approxA approxB)).g0 * (sourcePackedFourWords b : Int)) / (2 : Int) ^ (count + 1),
    ((sourceFactorWalk (count + 1) (sourceFactorInitial approxA approxB)).f1 * (sourcePackedFourWords a : Int) +
    (sourceFactorWalk (count + 1) (sourceFactorInitial approxA approxB)).g1 * (sourcePackedFourWords b : Int)) / (2 : Int) ^ (count + 1)) = _
  rw [TransferBlstArmInverseTraceRows01.symbolic_factor_walk_successor_is_the_last_factor_step]
  exact step

set_option pp.all true in
#check @scaled_value_divided_by_the_next_power_is_its_exact_signed_half
#print axioms scaled_value_divided_by_the_next_power_is_its_exact_signed_half
set_option pp.all true in
#check @doubled_tracked_row_divided_by_the_next_power_is_the_exact_signed_value
#print axioms doubled_tracked_row_divided_by_the_next_power_is_the_exact_signed_value
set_option pp.all true in
#check @original_controlled_coefficients_derive_the_complete_signed_control_step
#print axioms original_controlled_coefficients_derive_the_complete_signed_control_step
set_option pp.all true in
#check @original_four_word_factor_quotients_follow_the_exact_signed_control_step
#print axioms original_four_word_factor_quotients_follow_the_exact_signed_control_step
end ShielddSecurity.TransferBlstArmInverseRowTransition01
