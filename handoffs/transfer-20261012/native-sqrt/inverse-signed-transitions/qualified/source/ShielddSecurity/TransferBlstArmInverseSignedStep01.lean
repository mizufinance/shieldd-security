import ShielddSecurity.TransferBlstArmInverseWidthBudget01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSignedStep01

/-! UNRUN pure signed quotient transition chosen by the original natural
approximation controls. Bounded nonnegative scaled approximation errors
preserve a signed component within one error budget; signed maximum never
increases. Correspondence with original coefficient rows follows separately.
Total31-bit pair progress and compiled native instructions remain open. -/

def sourceSignedControlStep (p q : Nat) (x y : Int) : Int × Int :=
  if p % 2 = 0 then (x / 2, y)
  else if q ≤ p then ((x - y) / 2, y)
  else ((y - x) / 2, x)

theorem scaled_observation_outside_the_error_budget_is_strictly_above_the_budget
    (value : Int) (approx scale budget : Nat)
    (error : (value - (scale : Int) * (approx : Int)).natAbs ≤ budget)
    (outside : budget < value.natAbs) : (budget : Int) < value := by
  have both := TransferBlstArmInverseOrderGap01.signed_error_natabs_bound_derives_both_integer_budget_bounds _ _ error
  have nonnegative : 0 ≤ (scale : Int) * (approx : Int) := by
    rw [←Int.natCast_mul]
    omega
  by_cases positive : 0 ≤ value
  · have exactValue := Int.eq_natAbs_of_nonneg positive
    omega
  · have exactValue := Int.eq_neg_natAbs_of_nonpos (show value ≤ 0 by omega)
    omega

theorem original_signed_control_step_preserves_a_component_within_one_error_budget
    (x y : Int) (p q scale budget : Nat)
    (small : min x.natAbs y.natAbs ≤ budget)
    (leftError : (x - (scale : Int) * (p : Int)).natAbs ≤ budget)
    (rightError : (y - (scale : Int) * (q : Int)).natAbs ≤ budget) :
    min (sourceSignedControlStep p q x y).1.natAbs
      (sourceSignedControlStep p q x y).2.natAbs ≤ budget := by
  by_cases even : p % 2 = 0
  · simp only [sourceSignedControlStep, if_pos even]
    by_cases rightSmall : y.natAbs ≤ budget
    · exact Nat.le_trans (Nat.min_le_right _ _) rightSmall
    · have leftSmall : x.natAbs ≤ budget := by
        by_contra no
        have bothGreater : budget < min x.natAbs y.natAbs := Nat.lt_min.mpr ⟨by omega, by omega⟩
        omega
      have doubled : x.natAbs ≤ 2 * budget := by omega
      exact Nat.le_trans (Nat.min_le_left _ _)
        (TransferBlstArmInverseHalfGap01.symbolic_signed_gap_bounded_by_two_budgets_derives_the_half_gap_bound _ _ doubled)
  · by_cases ordered : q ≤ p
    · simp only [sourceSignedControlStep, if_neg even, if_pos ordered]
      by_cases rightSmall : y.natAbs ≤ budget
      · exact Nat.le_trans (Nat.min_le_right _ _) rightSmall
      · have leftSmall : x.natAbs ≤ budget := by
          by_contra no
          have bothGreater : budget < min x.natAbs y.natAbs := Nat.lt_min.mpr ⟨by omega, by omega⟩
          omega
        have upperX := TransferBlstArmInverseOrderGap01.signed_error_natabs_bound_derives_both_integer_budget_bounds _ _ leftSmall
        have lowerY := scaled_observation_outside_the_error_budget_is_strictly_above_the_budget y q scale budget rightError (by omega)
        have opposing : (y ≤ x ∧ p ≤ q) ∨ (x ≤ y ∧ q ≤ p) := Or.inr ⟨by omega, ordered⟩
        have gap := TransferBlstArmInverseOrderGap01.either_opposing_order_case_bounds_the_entire_actual_gap
          x y p q scale budget leftError rightError opposing
        exact Nat.le_trans (Nat.min_le_left _ _)
          (TransferBlstArmInverseHalfGap01.symbolic_signed_gap_bounded_by_two_budgets_derives_the_half_gap_bound _ _ gap)
    · simp only [sourceSignedControlStep, if_neg even, if_neg ordered]
      by_cases leftSmall : x.natAbs ≤ budget
      · exact Nat.le_trans (Nat.min_le_right _ _) leftSmall
      · have rightSmall : y.natAbs ≤ budget := by
          by_contra no
          have bothGreater : budget < min x.natAbs y.natAbs := Nat.lt_min.mpr ⟨by omega, by omega⟩
          omega
        have lowerX := scaled_observation_outside_the_error_budget_is_strictly_above_the_budget x p scale budget leftError (by omega)
        have upperY := TransferBlstArmInverseOrderGap01.signed_error_natabs_bound_derives_both_integer_budget_bounds _ _ rightSmall
        have opposing : (y ≤ x ∧ p ≤ q) ∨ (x ≤ y ∧ q ≤ p) := Or.inl ⟨by omega, by omega⟩
        have gap := TransferBlstArmInverseOrderGap01.either_opposing_order_case_bounds_the_entire_actual_gap
          x y p q scale budget leftError rightError opposing
        have reverseGap : (y - x).natAbs ≤ 2 * budget := by
          have identity : y - x = -(x - y) := by omega
          simpa only [identity, Int.natAbs_neg] using gap
        exact Nat.le_trans (Nat.min_le_left _ _)
          (TransferBlstArmInverseHalfGap01.symbolic_signed_gap_bounded_by_two_budgets_derives_the_half_gap_bound _ _ reverseGap)

theorem every_signed_control_step_does_not_increase_the_larger_magnitude
    (x y : Int) (p q : Nat) :
    max (sourceSignedControlStep p q x y).1.natAbs
      (sourceSignedControlStep p q x y).2.natAbs ≤ max x.natAbs y.natAbs := by
  have left := Nat.le_max_left x.natAbs y.natAbs
  have right := Nat.le_max_right x.natAbs y.natAbs
  have half : (x / 2).natAbs ≤ max x.natAbs y.natAbs :=
    TransferBlstArmInverseHalfGap01.symbolic_signed_gap_bounded_by_two_budgets_derives_the_half_gap_bound _ _ (by omega)
  have triangle := Int.natAbs_add_le x (-y)
  simp only [Int.natAbs_neg] at triangle
  have gap : (x - y).natAbs ≤ 2 * max x.natAbs y.natAbs := by
    have observed : (x - y).natAbs ≤ x.natAbs + y.natAbs := by
      simpa only [Int.sub_eq_add_neg] using triangle
    omega
  have halfGap := TransferBlstArmInverseHalfGap01.symbolic_signed_gap_bounded_by_two_budgets_derives_the_half_gap_bound _ _ gap
  have reverseGap : (y - x).natAbs ≤ 2 * max x.natAbs y.natAbs := by
    have identity : y - x = -(x - y) := by omega
    simpa only [identity, Int.natAbs_neg] using gap
  have reverseHalf := TransferBlstArmInverseHalfGap01.symbolic_signed_gap_bounded_by_two_budgets_derives_the_half_gap_bound _ _ reverseGap
  by_cases even : p % 2 = 0
  · simp only [sourceSignedControlStep, if_pos even]
    exact Nat.max_le_of_le_of_le half right
  · by_cases ordered : q ≤ p
    · simp only [sourceSignedControlStep, if_neg even, if_pos ordered]
      exact Nat.max_le_of_le_of_le halfGap right
    · simp only [sourceSignedControlStep, if_neg even, if_neg ordered]
      exact Nat.max_le_of_le_of_le reverseHalf left

set_option pp.all true in
#check @sourceSignedControlStep
#print axioms sourceSignedControlStep
set_option pp.all true in
#check @scaled_observation_outside_the_error_budget_is_strictly_above_the_budget
#print axioms scaled_observation_outside_the_error_budget_is_strictly_above_the_budget
set_option pp.all true in
#check @original_signed_control_step_preserves_a_component_within_one_error_budget
#print axioms original_signed_control_step_preserves_a_component_within_one_error_budget
set_option pp.all true in
#check @every_signed_control_step_does_not_increase_the_larger_magnitude
#print axioms every_signed_control_step_does_not_increase_the_larger_magnitude
end ShielddSecurity.TransferBlstArmInverseSignedStep01
