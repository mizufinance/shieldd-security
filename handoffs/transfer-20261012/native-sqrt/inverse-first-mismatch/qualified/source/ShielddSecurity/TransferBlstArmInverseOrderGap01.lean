import Init.Data.Int.Order
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseOrderGap01

/-! UNRUN reusable arithmetic for the future first-divergence argument.
Opposing actual/approximate orders force the actual pair to be close when
both scaled errors are bounded. This does not locate a divergence, prove
the loop's lasting behavior, or establish 31-bit progress. -/

theorem signed_error_natabs_bound_derives_both_integer_budget_bounds
    (error : Int) (budget : Nat) (bounded : error.natAbs ≤ budget) :
    -(budget : Int) ≤ error ∧ error ≤ (budget : Int) := by
  have upper := Int.le_natAbs (a := error)
  have lower := Int.le_natAbs (a := -error)
  rw [Int.natAbs_neg] at lower
  omega

theorem opposing_scaled_orders_bound_the_entire_actual_gap
    (x y : Int) (p q scale budget : Nat)
    (leftError : (x - (scale : Int) * (p : Int)).natAbs ≤ budget)
    (rightError : (y - (scale : Int) * (q : Int)).natAbs ≤ budget)
    (actualOrder : y ≤ x) (approximateOrder : p ≤ q) :
    (x - y).natAbs ≤ 2 * budget := by
  have left := signed_error_natabs_bound_derives_both_integer_budget_bounds _ _ leftError
  have right := signed_error_natabs_bound_derives_both_integer_budget_bounds _ _ rightError
  have castOrder : (p : Int) ≤ (q : Int) := by omega
  have scaleNonnegative : (0 : Int) ≤ (scale : Int) := by omega
  have scaledOrder := Int.mul_le_mul_of_nonneg_left castOrder scaleNonnegative
  have gapNonnegative : 0 ≤ x - y := by omega
  have gapValue := Int.eq_natAbs_of_nonneg gapNonnegative
  omega

theorem either_opposing_order_case_bounds_the_entire_actual_gap
    (x y : Int) (p q scale budget : Nat)
    (leftError : (x - (scale : Int) * (p : Int)).natAbs ≤ budget)
    (rightError : (y - (scale : Int) * (q : Int)).natAbs ≤ budget)
    (opposing : (y ≤ x ∧ p ≤ q) ∨ (x ≤ y ∧ q ≤ p)) :
    (x - y).natAbs ≤ 2 * budget := by
  rcases opposing with first | second
  · exact opposing_scaled_orders_bound_the_entire_actual_gap x y p q scale budget
      leftError rightError first.1 first.2
  · have reversed := opposing_scaled_orders_bound_the_entire_actual_gap y x q p scale budget
      rightError leftError second.1 second.2
    have identity : x - y = -(y - x) := by omega
    rw [identity, Int.natAbs_neg]
    exact reversed

set_option pp.all true in
#check @signed_error_natabs_bound_derives_both_integer_budget_bounds
#print axioms signed_error_natabs_bound_derives_both_integer_budget_bounds
set_option pp.all true in
#check @opposing_scaled_orders_bound_the_entire_actual_gap
#print axioms opposing_scaled_orders_bound_the_entire_actual_gap
set_option pp.all true in
#check @either_opposing_order_case_bounds_the_entire_actual_gap
#print axioms either_opposing_order_case_bounds_the_entire_actual_gap
end ShielddSecurity.TransferBlstArmInverseOrderGap01
