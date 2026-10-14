import ShielddSecurity.TransferBlstArmInverseNextRow01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseMinWalk01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorStep sourceFactorWalk)

/-! UNRUN symbolic lasting minimum for the original natural approximation
recurrence. Every source branch preserves a small coordinate, including the
exchange branch. This is not yet a bound on full signed input quotients or
31-bit batch progress, and asserts no compiled native correspondence. -/

theorem two_component_bounds_derive_the_exact_minimum_order
    (a b c d : Nat) (left : a ≤ c) (right : b ≤ d) :
    min a b ≤ min c d := by
  exact Nat.le_min_of_le_of_le
    (Nat.le_trans (Nat.min_le_left a b) left)
    (Nat.le_trans (Nat.min_le_right a b) right)

theorem every_original_factor_step_does_not_increase_its_natural_minimum
    (s : SourceFactors) :
    min (sourceFactorStep s).a (sourceFactorStep s).b ≤ min s.a s.b := by
  by_cases even : s.a % 2 = 0
  · simp only [sourceFactorStep, if_pos even]
    exact two_component_bounds_derive_the_exact_minimum_order _ _ _ _
      (Nat.div_le_self s.a 2) (Nat.le_refl s.b)
  · by_cases ordered : s.b ≤ s.a
    · simp only [sourceFactorStep, if_neg even, if_pos ordered]
      exact two_component_bounds_derive_the_exact_minimum_order _ _ _ _
        (Nat.le_trans (Nat.div_le_self (s.a - s.b) 2) (Nat.sub_le s.a s.b))
        (Nat.le_refl s.b)
    · simp only [sourceFactorStep, if_neg even, if_neg ordered]
      have bound := two_component_bounds_derive_the_exact_minimum_order _ _ _ _
        (Nat.le_trans (Nat.div_le_self (s.b - s.a) 2) (Nat.sub_le s.b s.a))
        (Nat.le_refl s.a)
      simpa only [Nat.min_comm] using bound

theorem every_symbolic_factor_walk_preserves_its_initial_natural_minimum_bound
    (count : Nat) (s : SourceFactors) :
    min (sourceFactorWalk count s).a (sourceFactorWalk count s).b ≤ min s.a s.b := by
  induction count generalizing s with
  | zero => exact Nat.le_refl _
  | succ count ih =>
      exact Nat.le_trans (ih (sourceFactorStep s))
        (every_original_factor_step_does_not_increase_its_natural_minimum s)

theorem symbolic_original_factor_walk_composes_at_any_prefix
    (before after : Nat) (s : SourceFactors) :
    sourceFactorWalk (before + after) s =
      sourceFactorWalk after (sourceFactorWalk before s) := by
  induction before generalizing s with
  | zero => simp only [Nat.zero_add, sourceFactorWalk]
  | succ before ih =>
      simpa only [Nat.succ_add, sourceFactorWalk] using ih (sourceFactorStep s)

set_option pp.all true in
#check @two_component_bounds_derive_the_exact_minimum_order
#print axioms two_component_bounds_derive_the_exact_minimum_order
set_option pp.all true in
#check @every_original_factor_step_does_not_increase_its_natural_minimum
#print axioms every_original_factor_step_does_not_increase_its_natural_minimum
set_option pp.all true in
#check @every_symbolic_factor_walk_preserves_its_initial_natural_minimum_bound
#print axioms every_symbolic_factor_walk_preserves_its_initial_natural_minimum_bound
set_option pp.all true in
#check @symbolic_original_factor_walk_composes_at_any_prefix
#print axioms symbolic_original_factor_walk_composes_at_any_prefix
end ShielddSecurity.TransferBlstArmInverseMinWalk01
