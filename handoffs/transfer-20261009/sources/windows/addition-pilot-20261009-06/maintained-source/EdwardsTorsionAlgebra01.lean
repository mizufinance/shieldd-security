import ShielddSecurity.EdwardsWeierstrassEquiv01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsTorsionAlgebra01
open EdwardsWeierstrassAlgebra01 EdwardsWeierstrassEquiv01
variable {F : Type} [Field F]

theorem forward_torsion_x (B x y : F) (minus : 1 - y ≠ 0) (plus : 1 + y ≠ 0) :
    forwardX B (-x) (-y) * forwardX B x y = B * B := by
  unfold forwardX
  field_simp [minus, plus]
  ring

theorem forward_torsion_y (B x y : F) (nonzeroX : x ≠ 0)
    (minus : 1 - y ≠ 0) (plus : 1 + y ≠ 0) :
    forwardY B (-x) (-y) * forwardX B x y ^ 2 = -B * B * forwardY B x y := by
  unfold forwardX forwardY
  field_simp [nonzeroX, minus, plus]
  ring

theorem origin_secant_x (A B X Y : F) (nonzeroX : X ≠ 0)
    (equation : Equation A B X Y) :
    (Y / X) ^ 2 - A * B - X = B * B / X := by
  unfold Equation at equation
  field_simp [nonzeroX]
  linear_combination equation

theorem origin_secant_y (B X Y : F) (nonzeroX : X ≠ 0) :
    -(Y / X) * (B * B / X) = -B * B * Y / X ^ 2 := by
  field_simp [nonzeroX] <;> ring

theorem plus_quadratic_nonzero (params : Parameters F) (y : F) :
    1 + params.d * y * y ≠ 0 := by
  intro zero
  apply params.nonSquare (params.imaginary * y)
  calc
    _ = (params.imaginary * params.imaginary) * (params.d * y * y) := by ring
    _ = -(params.d * y * y) := by rw [params.imaginarySquare]; ring
    _ = 1 := by linear_combination -zero

theorem same_y_square (params : Parameters F) (left right : Edwards params)
    (same : left.val.y = right.val.y) : left.val.x * left.val.x = right.val.x * right.val.x := by
  have hl := left.property
  have hr := right.property
  unfold Group.OnCurve at hl hr
  rw [← same] at hr
  have factored : (1 + params.d * left.val.y * left.val.y) *
      (left.val.x * left.val.x - right.val.x * right.val.x) = 0 := by
    linear_combination hr - hl
  exact sub_eq_zero.mp ((mul_eq_zero.mp factored).resolve_left
    (plus_quadratic_nonzero params left.val.y))

theorem same_y_x_or_neg (params : Parameters F) (left right : Edwards params)
    (same : left.val.y = right.val.y) :
    left.val.x = right.val.x ∨ left.val.x = -right.val.x := by
  have square := same_y_square params left right same
  have factored : (left.val.x - right.val.x) * (left.val.x + right.val.x) = 0 := by
    linear_combination square
  rcases mul_eq_zero.mp factored with equal | opposite
  · exact Or.inl (sub_eq_zero.mp equal)
  · exact Or.inr (eq_neg_of_add_eq_zero_left opposite)

theorem forward_x_difference (B x₁ x₂ y₁ y₂ : F)
    (minus₁ : 1 - y₁ ≠ 0) (minus₂ : 1 - y₂ ≠ 0) :
    (forwardX B x₁ y₁ - forwardX B x₂ y₂) * (1 - y₁) * (1 - y₂) =
      2 * B * (y₁ - y₂) := by
  unfold forwardX
  field_simp [minus₁, minus₂]
  ring

theorem forward_x_eq_iff (B x₁ x₂ y₁ y₂ : F) (two : (2 : F) ≠ 0) (nonzeroB : B ≠ 0)
    (minus₁ : 1 - y₁ ≠ 0) (minus₂ : 1 - y₂ ≠ 0) :
    forwardX B x₁ y₁ = forwardX B x₂ y₂ ↔ y₁ = y₂ := by
  constructor
  · intro same
    have equation := forward_x_difference B x₁ x₂ y₁ y₂ minus₁ minus₂
    rw [same, sub_self, zero_mul, zero_mul] at equation
    exact sub_eq_zero.mp ((mul_eq_zero.mp equation.symm).resolve_left (mul_ne_zero two nonzeroB))
  · intro same
    simp [forwardX, same]

end ShielddSecurity.EdwardsTorsionAlgebra01
