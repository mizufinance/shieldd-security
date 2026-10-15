import ShielddSecurity.TransferBlstArmInverseNaturalScale01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseApproxOrderBudget01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFirstMismatch01 (sourceFirstControlMismatch)

/-! UNRUN comparison mismatch also bounds the approximation gap itself.
Positive source scale cancels from both error budgets. Original first-mismatch
parity, rows and complete input errors derive that bound without new supplied
observations. Initial-size implications and total pair progress follow later. -/

theorem opposing_orders_and_positive_scaled_errors_bound_the_approximation_gap
    (x y : Int) (p q scale budget : Nat) (positive : 0 < scale)
    (leftError : (x - (scale : Int) * (p : Int)).natAbs ≤ scale * budget)
    (rightError : (y - (scale : Int) * (q : Int)).natAbs ≤ scale * budget)
    (actualOrder : y ≤ x) (approximateOrder : p ≤ q) :
    ((p : Int) - (q : Int)).natAbs ≤ 2 * budget := by
  have left := TransferBlstArmInverseOrderGap01.signed_error_natabs_bound_derives_both_integer_budget_bounds _ _ leftError
  have right := TransferBlstArmInverseOrderGap01.signed_error_natabs_bound_derives_both_integer_budget_bounds _ _ rightError
  simp only [Int.natCast_mul] at left right
  have multiplied : (scale : Int) * ((q : Int) - (p : Int)) ≤ (scale : Int) * (2 * (budget : Int)) := by
    rw [Int.mul_sub, Int.mul_left_comm (scale : Int) 2]
    omega
  have difference := Int.le_of_mul_le_mul_left multiplied (show 0 < (scale : Int) by omega)
  have nonnegative : 0 ≤ (q : Int) - (p : Int) := by omega
  have exactDifference := Int.eq_natAbs_of_nonneg nonnegative
  have identity : (p : Int) - (q : Int) = -((q : Int) - (p : Int)) := by omega
  rw [identity, Int.natAbs_neg]
  omega

theorem either_opposing_order_case_bounds_the_approximation_gap
    (x y : Int) (p q scale budget : Nat) (positive : 0 < scale)
    (leftError : (x - (scale : Int) * (p : Int)).natAbs ≤ scale * budget)
    (rightError : (y - (scale : Int) * (q : Int)).natAbs ≤ scale * budget)
    (opposing : (y ≤ x ∧ p ≤ q) ∨ (x ≤ y ∧ q ≤ p)) :
    ((p : Int) - (q : Int)).natAbs ≤ 2 * budget := by
  rcases opposing with first | second
  · exact opposing_orders_and_positive_scaled_errors_bound_the_approximation_gap
      x y p q scale budget positive leftError rightError first.1 first.2
  · have bound := opposing_orders_and_positive_scaled_errors_bound_the_approximation_gap
      y x q p scale budget positive rightError leftError second.1 second.2
    have identity : (p : Int) - (q : Int) = -((q : Int) - (p : Int)) := by omega
    simpa only [identity, Int.natAbs_neg] using bound

theorem original_first_control_mismatch_derives_the_approximation_gap_at_most_two_to32
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31)
    (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approximate := sourceFactorInitial (sourceApproxLow31 windows.1 a.w0) (sourceApproxLow31 windows.2 b.w0)
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    sourceFirstControlMismatch count approximate actual →
      (((sourceFactorWalk count approximate).a : Int) - ((sourceFactorWalk count approximate).b : Int)).natAbs ≤ 2 ^ 32 := by
  dsimp only
  intro first
  let approximate := sourceFactorWalk count (sourceFactorInitial
    (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
    (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))
  let actual := sourceFactorWalk count (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))
  have parity := TransferBlstArmInverseFirstParity01.original_inputs_and_earlier_control_synchronization_derive_both_natural_loop_parities
    count (sourceFourWordWindowWords a b).1 (sourceFourWordWindowWords a b).2 a b bounded oddB first.1
  have alignment := TransferBlstArmInverseTraceRows01.synchronized_initialized_prefix_identifies_both_signed_actual_quotients
    count (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
    (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
    (sourcePackedFourWords a) (sourcePackedFourWords b)
    (TransferBlstArmInverseFirstMismatch01.original_odd_low_word_derives_odd_entire_four_word_input b oddB) first.1
  have disagreement := TransferBlstArmInverseTraceRows01.matched_parity_and_different_controls_derive_strict_signed_comparison_disagreement
    actual approximate parity.1 (Ne.symm first.2)
  have errors := TransferBlstArmInverseWindowError01.original_source_produced_four_word_windows_derive_both_factor_prefix_error_bounds
    count a b (Nat.le_of_lt bounded) oddB
  have leftError : ((actual.a : Int) - ((2 ^ sourceFourWordWindowShift a b : Nat) : Int) * (approximate.a : Int)).natAbs ≤
      2 ^ sourceFourWordWindowShift a b * 2147483648 := by
    have observed := errors.1
    rw [alignment] at observed
    exact observed
  have rightError : ((actual.b : Int) - ((2 ^ sourceFourWordWindowShift a b : Nat) : Int) * (approximate.b : Int)).natAbs ≤
      2 ^ sourceFourWordWindowShift a b * 2147483648 := by
    have observed := errors.2
    rw [alignment] at observed
    exact observed
  have bound := either_opposing_order_case_bounds_the_approximation_gap
    (actual.a : Int) (actual.b : Int) approximate.a approximate.b
    (2 ^ sourceFourWordWindowShift a b) 2147483648 (Nat.two_pow_pos _) leftError rightError
    (TransferBlstArmInverseOrderStep01.strict_comparison_disagreement_derives_the_opposing_order_gap_premise _ _ _ _ disagreement)
  have budget : 2 * 2147483648 = (2 : Nat) ^ 32 := by decide +kernel
  rw [budget] at bound
  exact bound

set_option pp.all true in
#check @opposing_orders_and_positive_scaled_errors_bound_the_approximation_gap
#print axioms opposing_orders_and_positive_scaled_errors_bound_the_approximation_gap
set_option pp.all true in
#check @either_opposing_order_case_bounds_the_approximation_gap
#print axioms either_opposing_order_case_bounds_the_approximation_gap
set_option pp.all true in
#check @original_first_control_mismatch_derives_the_approximation_gap_at_most_two_to32
#print axioms original_first_control_mismatch_derives_the_approximation_gap_at_most_two_to32
end ShielddSecurity.TransferBlstArmInverseApproxOrderBudget01
