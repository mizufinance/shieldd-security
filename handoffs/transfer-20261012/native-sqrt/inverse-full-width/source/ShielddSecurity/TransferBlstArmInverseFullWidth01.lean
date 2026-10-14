import ShielddSecurity.TransferBlstArmInverseFullWindowBounds01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseFullWidth01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords sourceSecondWindowChoice)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseTraceRows01 (sourceFactorControl)

/-! UNRUN exact joint full-input width, clipped below at64 as in the original
window algorithm. log2+1's zero convention is immaterial after this clipping.
Full upper/lower input powers and zero-window fallback derive the width from
original words. The first-mismatch final component is31 bits below this
initial width. Total pair bitlength progress and native execution remain open. -/

def sourceClippedJointBitwidth (a b : SourceFourWords) : Nat :=
  max 64 (max ((sourcePackedFourWords a).log2 + 1) ((sourcePackedFourWords b).log2 + 1))

theorem positive_upper_power_bounds_log2_plus_one
    (input width : Nat) (positive : 0 < width) (upper : input < 2 ^ width) :
    input.log2 + 1 ≤ width := by
  by_cases zero : input = 0
  · subst input
    change 1 ≤ width
    omega
  · have strict := (Nat.log2_lt zero).mpr upper
    omega

theorem lower_power_bounds_the_exact_log2
    (input power : Nat) (lower : 2 ^ power ≤ input) : power ≤ input.log2 := by
  have positive : 0 < input := Nat.lt_of_lt_of_le (Nat.two_pow_pos power) lower
  by_contra wrong
  have strict : input.log2 < power := by omega
  have smaller := (Nat.log2_lt (Nat.ne_of_gt positive)).mp strict
  omega

theorem original_computed_shift_plus64_is_the_exact_clipped_full_input_joint_bitwidth
    (a b : SourceFourWords) :
    sourceFourWordWindowShift a b + 64 = sourceClippedJointBitwidth a b := by
  have upper := TransferBlstArmInverseWindowMagnitude01.original_source_selected_window_derives_both_full_input_upper_power_bounds a b
  have left := positive_upper_power_bounds_log2_plus_one _ _ (by omega) upper.1
  have right := positive_upper_power_bounds_log2_plus_one _ _ (by omega) upper.2
  have widthUpper : sourceClippedJointBitwidth a b ≤ sourceFourWordWindowShift a b + 64 := by
    exact Nat.max_le_of_le_of_le (by omega) (Nat.max_le_of_le_of_le left right)
  have widthLower : sourceFourWordWindowShift a b + 64 ≤ sourceClippedJointBitwidth a b := by
    by_cases zero : (sourceSecondWindowChoice a b).highA ||| (sourceSecondWindowChoice a b).highB = 0
    · rw [TransferBlstArmInverseFullWindowBounds01.original_zero_selected_upper_window_has_exactly_zero_source_shift a b zero]
      exact Nat.le_max_left _ _
    · have lower := TransferBlstArmInverseFullWindowBounds01.original_nonzero_selected_upper_window_derives_a_full_input_lower_power a b zero
      rcases lower with lowA | lowB
      · have logs := lower_power_bounds_the_exact_log2 _ _ lowA
        exact Nat.le_trans (by omega)
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      · have logs := lower_power_bounds_the_exact_log2 _ _ lowB
        exact Nat.le_trans (by omega)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  exact Nat.le_antisymm widthLower widthUpper

theorem original31_final_cases_identify_the_small_component_bound_at_the_actual_clipped_bitwidth
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approxA := sourceApproxLow31 windows.1 a.w0
    let approxB := sourceApproxLow31 windows.2 b.w0
    let approximate := sourceFactorInitial approxA approxB
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    let final := sourceActualFactorQuotients 31 approxA approxB
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    ((∀ index < 31, sourceFactorControl (sourceFactorWalk index approximate) =
        sourceFactorControl (sourceFactorWalk index actual)) ∧
      final = (((sourceFactorWalk 31 actual).a : Int), ((sourceFactorWalk 31 actual).b : Int))) ∨
      min final.1.natAbs final.2.natAbs < 2 ^ (sourceClippedJointBitwidth a b - 31) := by
  dsimp only
  have finalCases := TransferBlstArmInverseFinalCases01.original31_controls_derive_exact_final_alignment_or_a_strict_small_signed_component a b oddB
  have width := original_computed_shift_plus64_is_the_exact_clipped_full_input_joint_bitwidth a b
  have exponent : sourceFourWordWindowShift a b + 33 = sourceClippedJointBitwidth a b - 31 := by omega
  rw [exponent] at finalCases
  exact finalCases

set_option pp.all true in
#check @sourceClippedJointBitwidth
#print axioms sourceClippedJointBitwidth
set_option pp.all true in
#check @positive_upper_power_bounds_log2_plus_one
#print axioms positive_upper_power_bounds_log2_plus_one
set_option pp.all true in
#check @lower_power_bounds_the_exact_log2
#print axioms lower_power_bounds_the_exact_log2
set_option pp.all true in
#check @original_computed_shift_plus64_is_the_exact_clipped_full_input_joint_bitwidth
#print axioms original_computed_shift_plus64_is_the_exact_clipped_full_input_joint_bitwidth
set_option pp.all true in
#check @original31_final_cases_identify_the_small_component_bound_at_the_actual_clipped_bitwidth
#print axioms original31_final_cases_identify_the_small_component_bound_at_the_actual_clipped_bitwidth
end ShielddSecurity.TransferBlstArmInverseFullWidth01
