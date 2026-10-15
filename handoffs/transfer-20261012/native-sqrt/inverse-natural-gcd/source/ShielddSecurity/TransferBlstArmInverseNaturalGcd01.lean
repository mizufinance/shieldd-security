import ShielddSecurity.TransferBlstArmInverseMagnitudeSchedule01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseNaturalGcd01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorStep sourceFactorWalk)
open TransferBlstArmInverseSignedStep01 (sourceSignedControlStep)

/-! Exact natural tail GCD. Natural factor updates agree with the signed
control step on nonnegative inputs, so the already proved signed GCD lemma
and symbolic induction preserve GCD for every exact tail length. A terminal
pair with unit initial GCD has second value1. Native execution stays open. -/

theorem the_original_natural_factor_step_is_the_signed_step_on_its_nonnegative_values
    (s : SourceFactors) :
    (((sourceFactorStep s).a : Int), ((sourceFactorStep s).b : Int)) =
      sourceSignedControlStep s.a s.b (s.a : Int) (s.b : Int) := by
  unfold sourceFactorStep sourceSignedControlStep
  by_cases even : s.a % 2 = 0
  · simp only [if_pos even]
    exact Prod.ext (by omega) rfl
  · simp only [if_neg even]
    by_cases order : s.b ≤ s.a
    · simp only [if_pos order]
      exact Prod.ext (by omega) rfl
    · simp only [if_neg order]
      exact Prod.ext (by omega) rfl

theorem every_original_natural_factor_step_with_odd_second_input_preserves_gcd
    (s : SourceFactors) (odd : s.b % 2 = 1) :
    Nat.gcd (sourceFactorStep s).a (sourceFactorStep s).b = Nat.gcd s.a s.b := by
  have compatible := the_original_natural_factor_step_is_the_signed_step_on_its_nonnegative_values s
  have preserved := TransferBlstArmInverseControlledGcd01.matched_parity_and_odd_second_value_make_the_original_signed_control_step_preserve_gcd
    (s.a : Int) (s.b : Int) s.a s.b (by omega) rfl
  rw [←compatible] at preserved
  exact preserved

theorem every_original_natural_factor_walk_with_odd_second_input_preserves_the_entire_gcd
    (count : Nat) (s : SourceFactors) (odd : s.b % 2 = 1) :
    Nat.gcd (sourceFactorWalk count s).a (sourceFactorWalk count s).b = Nat.gcd s.a s.b := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih =>
    have previous := ih (sourceFactorStep s)
      (TransferBlstArmInverseFactors01.original_factor_step_retains_odd_second_input s odd)
    have one := every_original_natural_factor_step_with_odd_second_input_preserves_gcd s odd
    exact previous.trans one

theorem an_exact_natural_tail_with_unit_initial_gcd_and_zero_first_output_has_second_output_one
    (count : Nat) (s : SourceFactors) (odd : s.b % 2 = 1) (unit : Nat.gcd s.a s.b = 1)
    (terminal : (sourceFactorWalk count s).a = 0) : (sourceFactorWalk count s).b = 1 := by
  have preserved := every_original_natural_factor_walk_with_odd_second_input_preserves_the_entire_gcd count s odd
  rw [terminal, Nat.gcd_zero_left, unit] at preserved
  exact preserved

set_option pp.all true in
#check @the_original_natural_factor_step_is_the_signed_step_on_its_nonnegative_values
#print axioms the_original_natural_factor_step_is_the_signed_step_on_its_nonnegative_values
set_option pp.all true in
#check @every_original_natural_factor_step_with_odd_second_input_preserves_gcd
#print axioms every_original_natural_factor_step_with_odd_second_input_preserves_gcd
set_option pp.all true in
#check @every_original_natural_factor_walk_with_odd_second_input_preserves_the_entire_gcd
#print axioms every_original_natural_factor_walk_with_odd_second_input_preserves_the_entire_gcd
set_option pp.all true in
#check @an_exact_natural_tail_with_unit_initial_gcd_and_zero_first_output_has_second_output_one
#print axioms an_exact_natural_tail_with_unit_initial_gcd_and_zero_first_output_has_second_output_one
end ShielddSecurity.TransferBlstArmInverseNaturalGcd01
