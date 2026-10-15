import ShielddSecurity.TransferBlstArmInverseBitlengthBudget01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePairPowerProgress01
open TransferBlstArmInverseBitlengthBudget01 (sourceNatBitlength)

/-! Generic exact pair bitlength decrease from the sharp source mismatch
bounds. Explicit lower, upper and width premises are composed with original
window facts separately. No native execution or iteration schedule claim. -/

theorem an_initial_minimum_and_two_error_budgets_bound_the_final_maximum_bitlength
    (initialMinimum finalMaximum width : Nat) (wide : 33 ≤ width)
    (lower : 2 ^ (width - 33) ≤ initialMinimum)
    (upper : finalMaximum ≤ initialMinimum + 2 ^ (width - 32)) :
    sourceNatBitlength finalMaximum ≤ sourceNatBitlength initialMinimum + 1 := by
  have bitLower := TransferBlstArmInverseBitlengthBudget01.a_positive_lower_power_bounds_the_exact_natural_bitlength _ _ lower
  have powerOrder : width - 32 ≤ sourceNatBitlength initialMinimum := by omega
  have budget := Nat.pow_le_pow_right Nat.zero_lt_two powerOrder
  have inputUpper := TransferBlstArmInverseBitlengthBudget01.every_natural_value_is_strictly_below_its_exact_bitlength_power initialMinimum
  apply TransferBlstArmInverseBitlengthBudget01.a_strict_upper_power_bounds_the_exact_natural_bitlength
  rw [Nat.pow_succ]
  omega

theorem sharp_minimum_and_maximum_bounds_decrease_the_total_pair_bitlength_by31
    (initialMinimum finalLeft finalRight width : Nat) (wide : 33 ≤ width)
    (lower : 2 ^ (width - 33) ≤ initialMinimum)
    (small : min finalLeft finalRight ≤ 2 ^ (width - 33))
    (large : max finalLeft finalRight ≤ initialMinimum + 2 ^ (width - 32)) :
    sourceNatBitlength finalLeft + sourceNatBitlength finalRight + 31 ≤
      width + sourceNatBitlength initialMinimum := by
  have smallBits := TransferBlstArmInverseBitlengthBudget01.a_value_at_most_a_power_has_bitlength_at_most_exponent_plus_one _ _ small
  have largeBits := an_initial_minimum_and_two_error_budgets_bound_the_final_maximum_bitlength _ _ _ wide lower large
  rw [TransferBlstArmInverseBitlengthBudget01.the_sum_of_exact_pair_bitlengths_equals_the_sum_for_the_minimum_and_maximum]
  omega

set_option pp.all true in
#check @an_initial_minimum_and_two_error_budgets_bound_the_final_maximum_bitlength
#print axioms an_initial_minimum_and_two_error_budgets_bound_the_final_maximum_bitlength
set_option pp.all true in
#check @sharp_minimum_and_maximum_bounds_decrease_the_total_pair_bitlength_by31
#print axioms sharp_minimum_and_maximum_bounds_decrease_the_total_pair_bitlength_by31
end ShielddSecurity.TransferBlstArmInversePairPowerProgress01
