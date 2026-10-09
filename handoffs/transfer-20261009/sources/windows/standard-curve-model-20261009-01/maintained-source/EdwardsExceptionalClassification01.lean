import ShielddSecurity.EdwardsAdditionPilot01
import ShielddSecurity.EdwardsTorsionAlgebra01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsExceptionalClassification01
open EdwardsWeierstrassEquiv01
variable {F : Type} [Field F]

/-- A vanishing x numerator forces equal y squares, without assuming a group cancellation law. -/
theorem cross_zero_y_square (params : Parameters F) (left right : Edwards params)
    (zero : Group.cross left.val right.val = 0) :
    left.val.y * left.val.y = right.val.y * right.val.y := by
  have hl := left.property
  have hr := right.property
  unfold Group.OnCurve at hl hr
  have crossSquare : left.val.x ^ 2 * right.val.y ^ 2 -
      left.val.y ^ 2 * right.val.x ^ 2 = 0 := by
    calc
      _ = Group.cross left.val right.val *
        (left.val.x * right.val.y - left.val.y * right.val.x) := by
          unfold Group.cross; ring
      _ = 0 := by rw [zero]; ring
  have factored : (left.val.y * left.val.y - right.val.y * right.val.y) *
      (1 - params.d * (left.val.x * right.val.y) * (left.val.x * right.val.y)) = 0 := by
    linear_combination right.val.y ^ 2 * hl - left.val.y ^ 2 * hr +
      (1 + params.d * right.val.y ^ 2) * crossSquare
  have nonzero : 1 - params.d * (left.val.x * right.val.y) *
      (left.val.x * right.val.y) ≠ 0 := by
    intro equal
    exact params.nonSquare (left.val.x * right.val.y) (sub_eq_zero.mp equal).symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp factored).resolve_right nonzero)

theorem cross_zero_y_or_neg (params : Parameters F) (left right : Edwards params)
    (zero : Group.cross left.val right.val = 0) :
    left.val.y = right.val.y ∨ left.val.y = -right.val.y := by
  have square := cross_zero_y_square params left right zero
  have factored : (left.val.y - right.val.y) * (left.val.y + right.val.y) = 0 := by
    linear_combination square
  rcases mul_eq_zero.mp factored with equal | opposite
  · exact Or.inl (sub_eq_zero.mp equal)
  · exact Or.inr (eq_neg_of_add_eq_zero_left opposite)

end ShielddSecurity.EdwardsExceptionalClassification01
