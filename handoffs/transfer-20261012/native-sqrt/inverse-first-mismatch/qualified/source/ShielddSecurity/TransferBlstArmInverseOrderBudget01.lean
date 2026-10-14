import ShielddSecurity.TransferBlstArmInverseOrderGap01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseOrderBudget01
open TransferBlstArmInverseOrderGap01

/-! UNRUN small arithmetic application for first-divergence development.
The scale is the actual source-selected shift parameter. An opposing-order
premise and both prefix errors imply a closeness bound. No divergence
location, bitlength-width identification or 31-bit progress is asserted. -/

theorem doubled_scaled_low31_error_budget_is_the_exact_shifted_power
    (shift : Nat) : 2 * (2 ^ shift * 2147483648) = 2 ^ (shift + 32) := by
  have scale : (2 : Nat) ^ 32 = 2 * 2147483648 := by decide +kernel
  rw [Nat.pow_add, scale]
  omega

theorem either_ordering_mismatch_from_both_low31_prefix_errors_derives_the_entire_gap_bound
    (x y : Int) (p q shift : Nat)
    (leftError : (x - ((2 ^ shift : Nat) : Int) * (p : Int)).natAbs ≤ 2 ^ shift * 2147483648)
    (rightError : (y - ((2 ^ shift : Nat) : Int) * (q : Int)).natAbs ≤ 2 ^ shift * 2147483648)
    (opposing : (y ≤ x ∧ p ≤ q) ∨ (x ≤ y ∧ q ≤ p)) :
    (x - y).natAbs ≤ 2 ^ (shift + 32) := by
  have bounded := either_opposing_order_case_bounds_the_entire_actual_gap
    x y p q (2 ^ shift) (2 ^ shift * 2147483648) leftError rightError opposing
  rw [doubled_scaled_low31_error_budget_is_the_exact_shifted_power] at bounded
  exact bounded

set_option pp.all true in
#check @doubled_scaled_low31_error_budget_is_the_exact_shifted_power
#print axioms doubled_scaled_low31_error_budget_is_the_exact_shifted_power
set_option pp.all true in
#check @either_ordering_mismatch_from_both_low31_prefix_errors_derives_the_entire_gap_bound
#print axioms either_ordering_mismatch_from_both_low31_prefix_errors_derives_the_entire_gap_bound
end ShielddSecurity.TransferBlstArmInverseOrderBudget01
