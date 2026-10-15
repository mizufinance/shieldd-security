import ShielddSecurity.TransferBlstArmInverseMismatchOperands01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseMismatchMaximum01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseFirstMismatch01 (sourceFirstControlMismatch)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)

/-! The exact natural pair at a first mismatch has a small gap and a
nonincreasing minimum. Its maximum is therefore bounded by the initial
minimum plus two error budgets. The original signed continuation inherits
that bound. Native full-limb multiplication and pair bitlength remain open. -/

theorem a_natural_pair_with_bounded_signed_gap_bounds_its_maximum_by_its_minimum
    (x y budget : Nat) (gap : ((x : Int) - (y : Int)).natAbs ≤ budget) :
    max x y ≤ min x y + budget := by
  have both := TransferBlstArmInverseOrderGap01.signed_error_natabs_bound_derives_both_integer_budget_bounds _ _ gap
  by_cases order : x ≤ y
  · rw [Nat.max_eq_right order, Nat.min_eq_left order]
    omega
  · have reverse : y ≤ x := by omega
    rw [Nat.max_eq_left reverse, Nat.min_eq_right reverse]
    omega

theorem original_first_mismatch_natural_maximum_is_bounded_by_the_initial_minimum_plus_two_budgets
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1)
    (first : sourceFirstControlMismatch count
      (sourceFactorInitial (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))
      (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))) :
    let actual := sourceFactorWalk count (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))
    max actual.a actual.b ≤ min (sourcePackedFourWords a) (sourcePackedFourWords b) +
      2 ^ (sourceFourWordWindowShift a b + 32) := by
  dsimp only
  have gap := TransferBlstArmInverseFirstParity01.original_source_first_control_mismatch_derives_the_exact_loop_gap_without_a_parity_premise
    count a b bounded oddB first
  have localBound := a_natural_pair_with_bounded_signed_gap_bounds_its_maximum_by_its_minimum _ _ _ gap
  have monotone := TransferBlstArmInverseMinWalk01.every_symbolic_factor_walk_preserves_its_initial_natural_minimum_bound
    count (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))
  exact Nat.le_trans localBound (Nat.add_le_add_right monotone _)

theorem original_first_mismatch_final_signed_maximum_is_bounded_by_the_initial_minimum_plus_two_budgets
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1)
    (first : sourceFirstControlMismatch count
      (sourceFactorInitial (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))
      (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))) :
    let final := sourceActualFactorQuotients 31
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    max final.1.natAbs final.2.natAbs ≤ min (sourcePackedFourWords a) (sourcePackedFourWords b) +
      2 ^ (sourceFourWordWindowShift a b + 32) := by
  dsimp only
  have naturalBound := original_first_mismatch_natural_maximum_is_bounded_by_the_initial_minimum_plus_two_budgets count a b bounded oddB first
  have alignment := TransferBlstArmInverseTraceRows01.synchronized_initialized_prefix_identifies_both_signed_actual_quotients
    count (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
    (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
    (sourcePackedFourWords a) (sourcePackedFourWords b)
    (TransferBlstArmInverseFirstMismatch01.original_odd_low_word_derives_odd_entire_four_word_input b oddB) first.1
  have monotone := TransferBlstArmInverseSharpLasting01.original_signed_quotient_maximum_never_increases_from_any_earlier_prefix_through31
    count (31 - count) a b (by omega) oddB
  have index : count + (31 - count) = 31 := by omega
  dsimp only at monotone
  rw [index, alignment] at monotone
  have castLeft : ((sourceFactorWalk count (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))).a : Int).natAbs =
      (sourceFactorWalk count (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))).a := by rfl
  have castRight : ((sourceFactorWalk count (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))).b : Int).natAbs =
      (sourceFactorWalk count (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))).b := by rfl
  rw [castLeft, castRight] at monotone
  exact Nat.le_trans monotone naturalBound

set_option pp.all true in
#check @a_natural_pair_with_bounded_signed_gap_bounds_its_maximum_by_its_minimum
#print axioms a_natural_pair_with_bounded_signed_gap_bounds_its_maximum_by_its_minimum
set_option pp.all true in
#check @original_first_mismatch_natural_maximum_is_bounded_by_the_initial_minimum_plus_two_budgets
#print axioms original_first_mismatch_natural_maximum_is_bounded_by_the_initial_minimum_plus_two_budgets
set_option pp.all true in
#check @original_first_mismatch_final_signed_maximum_is_bounded_by_the_initial_minimum_plus_two_budgets
#print axioms original_first_mismatch_final_signed_maximum_is_bounded_by_the_initial_minimum_plus_two_budgets
end ShielddSecurity.TransferBlstArmInverseMismatchMaximum01
