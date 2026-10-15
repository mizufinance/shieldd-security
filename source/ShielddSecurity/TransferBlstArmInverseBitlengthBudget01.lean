import ShielddSecurity.TransferBlstArmInverseMismatchMaximum01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseBitlengthBudget01

/-! Exact natural bitlength, including zero, and small power-bound lemmas for
the source-model progress argument. No native instruction correspondence. -/

def sourceNatBitlength (value : Nat) : Nat :=
  if value = 0 then 0 else value.log2 + 1

theorem a_strict_upper_power_bounds_the_exact_natural_bitlength
    (value width : Nat) (upper : value < 2 ^ width) :
    sourceNatBitlength value ≤ width := by
  unfold sourceNatBitlength
  by_cases zero : value = 0
  · rw [if_pos zero]
    omega
  · rw [if_neg zero]
    have bound := (Nat.log2_lt zero).mpr upper
    omega

theorem every_natural_value_is_strictly_below_its_exact_bitlength_power
    (value : Nat) : value < 2 ^ sourceNatBitlength value := by
  unfold sourceNatBitlength
  by_cases zero : value = 0
  · rw [if_pos zero, zero]
    decide
  · rw [if_neg zero]
    exact Nat.lt_log2_self

theorem a_positive_lower_power_bounds_the_exact_natural_bitlength
    (value exponent : Nat) (lower : 2 ^ exponent ≤ value) :
    exponent + 1 ≤ sourceNatBitlength value := by
  have positive := Nat.lt_of_lt_of_le (Nat.two_pow_pos exponent) lower
  have bound := ShielddSecurity.TransferBlstArmInverseFullWidth01.lower_power_bounds_the_exact_log2 value exponent lower
  simp only [sourceNatBitlength, if_neg (Nat.ne_of_gt positive)]
  omega

theorem a_value_at_most_a_power_has_bitlength_at_most_exponent_plus_one
    (value exponent : Nat) (upper : value ≤ 2 ^ exponent) :
    sourceNatBitlength value ≤ exponent + 1 := by
  apply a_strict_upper_power_bounds_the_exact_natural_bitlength
  have positive := Nat.two_pow_pos exponent
  rw [Nat.pow_succ]
  omega

theorem the_exact_bitlength_is_monotone
    (left right : Nat) (order : left ≤ right) :
    sourceNatBitlength left ≤ sourceNatBitlength right := by
  have upper := every_natural_value_is_strictly_below_its_exact_bitlength_power right
  exact a_strict_upper_power_bounds_the_exact_natural_bitlength _ _ (Nat.lt_of_le_of_lt order upper)

theorem the_sum_of_exact_pair_bitlengths_equals_the_sum_for_the_minimum_and_maximum
    (left right : Nat) :
    sourceNatBitlength left + sourceNatBitlength right =
      sourceNatBitlength (min left right) + sourceNatBitlength (max left right) := by
  by_cases order : left ≤ right
  · rw [Nat.min_eq_left order, Nat.max_eq_right order]
  · have reverse : right ≤ left := by omega
    rw [Nat.min_eq_right reverse, Nat.max_eq_left reverse, Nat.add_comm]

set_option pp.all true in
#check @sourceNatBitlength
#print axioms sourceNatBitlength
set_option pp.all true in
#check @a_strict_upper_power_bounds_the_exact_natural_bitlength
#print axioms a_strict_upper_power_bounds_the_exact_natural_bitlength
set_option pp.all true in
#check @every_natural_value_is_strictly_below_its_exact_bitlength_power
#print axioms every_natural_value_is_strictly_below_its_exact_bitlength_power
set_option pp.all true in
#check @a_positive_lower_power_bounds_the_exact_natural_bitlength
#print axioms a_positive_lower_power_bounds_the_exact_natural_bitlength
set_option pp.all true in
#check @a_value_at_most_a_power_has_bitlength_at_most_exponent_plus_one
#print axioms a_value_at_most_a_power_has_bitlength_at_most_exponent_plus_one
set_option pp.all true in
#check @the_exact_bitlength_is_monotone
#print axioms the_exact_bitlength_is_monotone
set_option pp.all true in
#check @the_sum_of_exact_pair_bitlengths_equals_the_sum_for_the_minimum_and_maximum
#print axioms the_sum_of_exact_pair_bitlengths_equals_the_sum_for_the_minimum_and_maximum
end ShielddSecurity.TransferBlstArmInverseBitlengthBudget01
