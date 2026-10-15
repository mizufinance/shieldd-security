import ShielddSecurity.TransferBlstArmInverseBatchZero01
import Init.Data.Int.Gcd
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseControlledGcd01
open TransferBlstArmInverseSignedStep01 (sourceSignedControlStep)

/-! Small signed GCD lemmas for the original source control step. An odd
second value and matched first-control parity preserve the entire GCD,
including negative values and opposing comparison directions. Deriving
those premises for the original window trace and native execution follows
separately. -/

theorem every_signed_odd_value_is_coprime_to_two
    (value : Int) (odd : value % 2 = 1) : Int.gcd 2 value = 1 := by
  have absoluteOdd := TransferBlstArmInverseWindowBatchOdd01.a_signed_odd_value_has_an_odd_natural_magnitude value odd
  rw [Int.gcd_eq_natAbs_gcd_natAbs]
  change Nat.gcd 2 value.natAbs = 1
  rw [Nat.gcd_rec, absoluteOdd]
  decide +kernel

theorem exactly_halving_an_even_signed_value_preserves_gcd_with_an_odd_second_value
    (left right : Int) (even : left % 2 = 0) (odd : right % 2 = 1) :
    Int.gcd (left / 2) right = Int.gcd left right := by
  have doubled : 2 * (left / 2) = left := Int.mul_ediv_cancel_of_emod_eq_zero even
  have cancel := Int.gcd_mul_right_left_of_gcd_eq_one (n := 2) (m := right) (k := left / 2)
    (every_signed_odd_value_is_coprime_to_two right odd)
  rw [doubled] at cancel
  exact cancel.symm

theorem the_half_difference_of_two_signed_odd_values_preserves_the_entire_gcd
    (left right : Int) (leftOdd : left % 2 = 1) (rightOdd : right % 2 = 1) :
    Int.gcd ((left - right) / 2) right = Int.gcd left right := by
  have even : (left - right) % 2 = 0 := by omega
  rw [exactly_halving_an_even_signed_value_preserves_gcd_with_an_odd_second_value _ _ even rightOdd]
  exact Int.gcd_sub_self_left right left

theorem matched_parity_and_odd_second_value_make_the_original_signed_control_step_preserve_gcd
    (left right : Int) (p q : Nat) (odd : right % 2 = 1)
    (matched : left % 2 = (p : Int) % 2) :
    Int.gcd (sourceSignedControlStep p q left right).1 (sourceSignedControlStep p q left right).2 =
      Int.gcd left right := by
  unfold sourceSignedControlStep
  by_cases even : p % 2 = 0
  · rw [if_pos even]
    exact exactly_halving_an_even_signed_value_preserves_gcd_with_an_odd_second_value left right (by omega) odd
  · rw [if_neg even]
    have leftOdd : left % 2 = 1 := by omega
    by_cases order : q ≤ p
    · rw [if_pos order]
      exact the_half_difference_of_two_signed_odd_values_preserves_the_entire_gcd left right leftOdd odd
    · rw [if_neg order]
      have reverse := the_half_difference_of_two_signed_odd_values_preserves_the_entire_gcd right left odd leftOdd
      exact reverse.trans (Int.gcd_comm right left)

set_option pp.all true in
#check @every_signed_odd_value_is_coprime_to_two
#print axioms every_signed_odd_value_is_coprime_to_two
set_option pp.all true in
#check @exactly_halving_an_even_signed_value_preserves_gcd_with_an_odd_second_value
#print axioms exactly_halving_an_even_signed_value_preserves_gcd_with_an_odd_second_value
set_option pp.all true in
#check @the_half_difference_of_two_signed_odd_values_preserves_the_entire_gcd
#print axioms the_half_difference_of_two_signed_odd_values_preserves_the_entire_gcd
set_option pp.all true in
#check @matched_parity_and_odd_second_value_make_the_original_signed_control_step_preserve_gcd
#print axioms matched_parity_and_odd_second_value_make_the_original_signed_control_step_preserve_gcd
end ShielddSecurity.TransferBlstArmInverseControlledGcd01
