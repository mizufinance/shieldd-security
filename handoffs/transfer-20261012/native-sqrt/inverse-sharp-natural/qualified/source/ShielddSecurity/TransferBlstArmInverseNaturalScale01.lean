import ShielddSecurity.TransferBlstArmInverseSharpLasting01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseNaturalScale01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorStep sourceFactorWalk)

/-! UNRUN symbolic natural approximation scale facts. Odd second input is
retained, and the pair sum can shrink by at most a factor of two per original
step. An initial64-bit high value and a below-low31 minimum therefore remain
too far apart for a comparison mismatch before31. Original-window input
production and opposing-order contradiction are composed separately. -/

theorem every_original_natural_factor_walk_retains_its_odd_second_input
    (count : Nat) (s : SourceFactors) (odd : s.b % 2 = 1) :
    (sourceFactorWalk count s).b % 2 = 1 := by
  induction count generalizing s with
  | zero => exact odd
  | succ count ih =>
      exact ih (sourceFactorStep s)
        (TransferBlstArmInverseFactors01.original_factor_step_retains_odd_second_input s odd)

theorem original_natural_factor_step_sum_shrinks_by_at_most_a_factor_of_two
    (s : SourceFactors) (odd : s.b % 2 = 1) :
    s.a + s.b ≤ 2 * ((sourceFactorStep s).a + (sourceFactorStep s).b) := by
  by_cases even : s.a % 2 = 0
  · simp only [sourceFactorStep, if_pos even]
    omega
  · by_cases ordered : s.b ≤ s.a
    · simp only [sourceFactorStep, if_neg even, if_pos ordered]
      omega
    · simp only [sourceFactorStep, if_neg even, if_neg ordered]
      omega

theorem every_original_natural_factor_walk_derives_its_symbolic_scaled_pair_sum_lower_bound
    (count : Nat) (s : SourceFactors) (odd : s.b % 2 = 1) :
    s.a + s.b ≤ 2 ^ count * ((sourceFactorWalk count s).a + (sourceFactorWalk count s).b) := by
  induction count generalizing s with
  | zero => simp only [sourceFactorWalk, Nat.pow_zero, Nat.one_mul]; exact Nat.le_refl _
  | succ count ih =>
      have next := ih (sourceFactorStep s)
        (TransferBlstArmInverseFactors01.original_factor_step_retains_odd_second_input s odd)
      calc
        _ ≤ 2 * ((sourceFactorStep s).a + (sourceFactorStep s).b) :=
          original_natural_factor_step_sum_shrinks_by_at_most_a_factor_of_two s odd
        _ ≤ 2 * (2 ^ count * ((sourceFactorWalk count (sourceFactorStep s)).a +
            (sourceFactorWalk count (sourceFactorStep s)).b)) := Nat.mul_le_mul_left 2 next
        _ = _ := by
          rw [Nat.pow_succ]
          simp only [sourceFactorWalk, Nat.mul_assoc, Nat.mul_left_comm]

theorem large_initial_approximation_sum_and_small_minimum_force_separation_before31
    (count : Nat) (s : SourceFactors) (bounded : count < 31) (odd : s.b % 2 = 1)
    (large : 2 ^ 63 ≤ s.a + s.b) (small : min s.a s.b < 2 ^ 31) :
    2 ^ 32 < (((sourceFactorWalk count s).a : Int) - ((sourceFactorWalk count s).b : Int)).natAbs := by
  let current := sourceFactorWalk count s
  have scaled := every_original_natural_factor_walk_derives_its_symbolic_scaled_pair_sum_lower_bound count s odd
  change s.a + s.b ≤ 2 ^ count * (current.a + current.b) at scaled
  have powerBound : (2 : Nat) ^ count ≤ 2 ^ 30 := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have sumLower : 2 ^ 33 ≤ current.a + current.b := by
    by_contra no
    have sumSmall : current.a + current.b < 2 ^ 33 := by omega
    have product : 2 ^ count * (current.a + current.b) < 2 ^ count * 2 ^ 33 :=
      Nat.mul_lt_mul_of_pos_left sumSmall (Nat.two_pow_pos count)
    have productUpper : 2 ^ count * 2 ^ 33 ≤ 2 ^ 30 * 2 ^ 33 :=
      Nat.mul_le_mul_right (2 ^ 33) powerBound
    have constant : (2 : Nat) ^ 30 * 2 ^ 33 = 2 ^ 63 := by decide +kernel
    rw [constant] at productUpper
    omega
  have monotone : min current.a current.b ≤ min s.a s.b :=
    TransferBlstArmInverseMinWalk01.every_symbolic_factor_walk_preserves_its_initial_natural_minimum_bound count s
  have minSmall : min current.a current.b < 2 ^ 31 := Nat.lt_of_le_of_lt monotone small
  change 2 ^ 32 < ((current.a : Int) - (current.b : Int)).natAbs
  by_contra no
  have gap : ((current.a : Int) - (current.b : Int)).natAbs ≤ 2 ^ 32 := by omega
  have both := TransferBlstArmInverseOrderGap01.signed_error_natabs_bound_derives_both_integer_budget_bounds _ _ gap
  by_cases ordered : current.a ≤ current.b
  · rw [Nat.min_eq_left ordered] at minSmall
    omega
  · have reverse : current.b ≤ current.a := by omega
    rw [Nat.min_eq_right reverse] at minSmall
    omega

set_option pp.all true in
#check @every_original_natural_factor_walk_retains_its_odd_second_input
#print axioms every_original_natural_factor_walk_retains_its_odd_second_input
set_option pp.all true in
#check @original_natural_factor_step_sum_shrinks_by_at_most_a_factor_of_two
#print axioms original_natural_factor_step_sum_shrinks_by_at_most_a_factor_of_two
set_option pp.all true in
#check @every_original_natural_factor_walk_derives_its_symbolic_scaled_pair_sum_lower_bound
#print axioms every_original_natural_factor_walk_derives_its_symbolic_scaled_pair_sum_lower_bound
set_option pp.all true in
#check @large_initial_approximation_sum_and_small_minimum_force_separation_before31
#print axioms large_initial_approximation_sum_and_small_minimum_force_separation_before31
end ShielddSecurity.TransferBlstArmInverseNaturalScale01
