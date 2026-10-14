import ShielddSecurity.TransferBlstArmInverseHalfGap01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseNextRow01
open TransferBlstArmInverseFactors01
  (SourceFactors sourceFactorInitial sourceFactorStep sourceFactorWalk)
open TransferBlstArmInverseTraceRows01 (sourceFactorControl sourceSameFactorRows)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseFirstMismatch01 (sourceFirstControlMismatch)

/-! UNRUN next modeled row at the first control mismatch. Symbolic row
identities connect the signed half-gap to the next coefficient quotient.
Original inputs and synchronized earlier controls derive every row premise.
Native word multiplication, lasting behavior and 31-bit progress remain open. -/

theorem odd_source_step_first_row_is_the_oriented_signed_half_gap
    (count : Nat) (s : SourceFactors) (inputA inputB x y : Int)
    (odd : s.a % 2 ≠ 0)
    (leftRow : (2 : Int) ^ count * x = s.f0 * inputA + s.g0 * inputB)
    (rightRow : (2 : Int) ^ count * y = s.f1 * inputA + s.g1 * inputB) :
    ((sourceFactorStep s).f0 * inputA + (sourceFactorStep s).g0 * inputB) /
      (2 : Int) ^ (count + 1) =
      if s.b ≤ s.a then (x - y) / 2 else (y - x) / 2 := by
  have positive : 0 < (2 : Int) ^ count := Int.pow_pos (by decide)
  by_cases ordered : s.b ≤ s.a
  · simp only [sourceFactorStep, if_neg odd, if_pos ordered]
    have numerator : (s.f0 - s.f1) * inputA + (s.g0 - s.g1) * inputB =
        (2 : Int) ^ count * (x - y) := by
      rw [Int.mul_sub, leftRow, rightRow, Int.sub_mul, Int.sub_mul]
      omega
    rw [numerator, Int.pow_succ]
    exact Int.mul_ediv_mul_of_pos _ _ positive
  · simp only [sourceFactorStep, if_neg odd, if_neg ordered]
    have numerator : (s.f1 - s.f0) * inputA + (s.g1 - s.g0) * inputB =
        (2 : Int) ^ count * (y - x) := by
      rw [Int.mul_sub, rightRow, leftRow, Int.sub_mul, Int.sub_mul]
      omega
    rw [numerator, Int.pow_succ]
    exact Int.mul_ediv_mul_of_pos _ _ positive

theorem odd_source_step_first_row_inherits_the_signed_gap_budget
    (count budget : Nat) (s : SourceFactors) (inputA inputB x y : Int)
    (odd : s.a % 2 ≠ 0)
    (leftRow : (2 : Int) ^ count * x = s.f0 * inputA + s.g0 * inputB)
    (rightRow : (2 : Int) ^ count * y = s.f1 * inputA + s.g1 * inputB)
    (gap : (x - y).natAbs ≤ 2 * budget) :
    (((sourceFactorStep s).f0 * inputA + (sourceFactorStep s).g0 * inputB) /
      (2 : Int) ^ (count + 1)).natAbs ≤ budget := by
  rw [odd_source_step_first_row_is_the_oriented_signed_half_gap
    count s inputA inputB x y odd leftRow rightRow]
  split
  · exact TransferBlstArmInverseHalfGap01.symbolic_signed_gap_bounded_by_two_budgets_derives_the_half_gap_bound _ _ gap
  · have reverseGap : (y - x).natAbs ≤ 2 * budget := by
      have identity : y - x = -(x - y) := by omega
      simpa only [identity, Int.natAbs_neg] using gap
    exact TransferBlstArmInverseHalfGap01.symbolic_signed_gap_bounded_by_two_budgets_derives_the_half_gap_bound _ _ reverseGap

theorem original_first_mismatch_next_controlled_quotient_has_the_derived_half_gap_bound
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31)
    (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approxA := sourceApproxLow31 windows.1 a.w0
    let approxB := sourceApproxLow31 windows.2 b.w0
    let approximate := sourceFactorInitial approxA approxB
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    sourceFirstControlMismatch count approximate actual →
      (sourceActualFactorQuotients (count + 1) approxA approxB
        (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)).1.natAbs ≤
        2 ^ (sourceFourWordWindowShift a b + 31) := by
  dsimp only
  intro first
  let approxA := sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0
  let approxB := sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0
  let approximate := sourceFactorWalk count (sourceFactorInitial approxA approxB)
  let actual := sourceFactorWalk count (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))
  have rows : sourceSameFactorRows approximate actual :=
    TransferBlstArmInverseTraceRows01.synchronized_earlier_prefix_controls_derive_equal_entire_factor_rows
      count _ _ ⟨rfl, rfl, rfl, rfl⟩ first.1
  have parity := TransferBlstArmInverseFirstParity01.original_inputs_and_earlier_control_synchronization_derive_both_natural_loop_parities
    count (sourceFourWordWindowWords a b).1 (sourceFourWordWindowWords a b).2 a b bounded oddB first.1
  have odd : approximate.a % 2 ≠ 0 := by
    intro even
    have actualEven : actual.a % 2 = 0 := parity.1.trans even
    have same : sourceFactorControl approximate = sourceFactorControl actual := by
      simp only [sourceFactorControl, if_pos even, if_pos actualEven]
    exact first.2 same
  have tracked := TransferBlstArmInverseFactors01.original_initialized_factor_walk_derives_exact_scaled_input_rows
    count (sourcePackedFourWords a) (sourcePackedFourWords b)
    (TransferBlstArmInverseFirstMismatch01.original_odd_low_word_derives_odd_entire_four_word_input b oddB)
  change (2 : Int) ^ count * (actual.a : Int) = actual.f0 * (sourcePackedFourWords a : Int) + actual.g0 * (sourcePackedFourWords b : Int) ∧
    (2 : Int) ^ count * (actual.b : Int) = actual.f1 * (sourcePackedFourWords a : Int) + actual.g1 * (sourcePackedFourWords b : Int) at tracked
  have leftRow : (2 : Int) ^ count * (actual.a : Int) =
      approximate.f0 * (sourcePackedFourWords a : Int) + approximate.g0 * (sourcePackedFourWords b : Int) := by
    rw [rows.1, rows.2.1]
    exact tracked.1
  have rightRow : (2 : Int) ^ count * (actual.b : Int) =
      approximate.f1 * (sourcePackedFourWords a : Int) + approximate.g1 * (sourcePackedFourWords b : Int) := by
    rw [rows.2.2.1, rows.2.2.2]
    exact tracked.2
  have gap := TransferBlstArmInverseFirstParity01.original_source_first_control_mismatch_derives_the_exact_loop_gap_without_a_parity_premise
    count a b bounded oddB first
  rw [TransferBlstArmInverseHalfGap01.original_first_mismatch_budget_is_exactly_twice_the_half_gap_budget] at gap
  have next := odd_source_step_first_row_inherits_the_signed_gap_budget count
    (2 ^ (sourceFourWordWindowShift a b + 31)) approximate
    (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    (actual.a : Int) (actual.b : Int) odd leftRow rightRow gap
  change (((sourceFactorWalk (count + 1) (sourceFactorInitial approxA approxB)).f0 * (sourcePackedFourWords a : Int) +
    (sourceFactorWalk (count + 1) (sourceFactorInitial approxA approxB)).g0 * (sourcePackedFourWords b : Int)) /
    (2 : Int) ^ (count + 1)).natAbs ≤ _
  rw [TransferBlstArmInverseTraceRows01.symbolic_factor_walk_successor_is_the_last_factor_step]
  exact next

set_option pp.all true in
#check @odd_source_step_first_row_is_the_oriented_signed_half_gap
#print axioms odd_source_step_first_row_is_the_oriented_signed_half_gap
set_option pp.all true in
#check @odd_source_step_first_row_inherits_the_signed_gap_budget
#print axioms odd_source_step_first_row_inherits_the_signed_gap_budget
set_option pp.all true in
#check @original_first_mismatch_next_controlled_quotient_has_the_derived_half_gap_bound
#print axioms original_first_mismatch_next_controlled_quotient_has_the_derived_half_gap_bound
end ShielddSecurity.TransferBlstArmInverseNextRow01
