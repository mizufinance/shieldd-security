import ShielddSecurity.ConcreteWeierstrassPoint01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointOperationRows01
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]

/-- Input equations and a nonvertical branch derive output membership from Mathlib. -/
theorem add_coordinates {x₁ x₂ y₁ y₂ : F}
    (left : curve.Equation x₁ y₁) (right : curve.Equation x₂ y₂)
    (nonvertical : ¬(x₁ = x₂ ∧ y₁ = curve.negY x₂ y₂)) :
    ∃ output : curve.Equation (curve.addX x₁ x₂ (curve.slope x₁ x₂ y₁ y₂))
        (curve.addY x₁ x₂ y₁ (curve.slope x₁ x₂ y₁ y₂)),
      WeierstrassCurve.Affine.Point.mk left + WeierstrassCurve.Affine.Point.mk right =
        WeierstrassCurve.Affine.Point.mk output := by
  have hl := curve.equation_iff_nonsingular.mp left
  have hr := curve.equation_iff_nonsingular.mp right
  have hOutput := curve.nonsingular_add hl hr nonvertical
  exact ⟨hOutput.1, WeierstrassCurve.Affine.Point.add_some nonvertical⟩

theorem secant_rows {x₁ x₂ y₁ y₂ slope outX outY : F}
    (left : curve.Equation x₁ y₁) (right : curve.Equation x₂ y₂) (different : x₁ ≠ x₂)
    (slopeRow : slope * (x₁ - x₂) = y₁ - y₂)
    (xRow : outX = slope ^ 2 - A * B - x₁ - x₂)
    (yRow : outY = slope * (x₁ - outX) - y₁) :
    ∃ output : curve.Equation outX outY,
      WeierstrassCurve.Affine.Point.mk left + WeierstrassCurve.Affine.Point.mk right =
        WeierstrassCurve.Affine.Point.mk output := by
  have slopeValue : curve.slope x₁ x₂ y₁ y₂ = slope := by
    rw [curve.slope_of_X_ne different]
    exact ((eq_div_iff (sub_ne_zero.mpr different)).mpr slopeRow).symm
  have xValue : curve.addX x₁ x₂ (curve.slope x₁ x₂ y₁ y₂) = outX := by
    rw [slopeValue]
    simpa [WeierstrassCurve.Affine.addX, curve] using xRow.symm
  have yValue : curve.addY x₁ x₂ y₁ (curve.slope x₁ x₂ y₁ y₂) = outY := by
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, xValue, slopeValue]
    simp only [WeierstrassCurve.Affine.negY, curve, zero_mul, sub_zero]
    linear_combination -yRow
  simpa only [xValue, yValue] using
    (add_coordinates left right (fun equal => different equal.1))

theorem tangent_rows {x y slope outX outY : F} (input : curve.Equation x y)
    (nonzero : (2 : F) * y ≠ 0)
    (slopeRow : slope * (2 * y) = 3 * x ^ 2 + 2 * (A * B) * x + B * B)
    (xRow : outX = slope ^ 2 - A * B - x - x)
    (yRow : outY = slope * (x - outX) - y) :
    ∃ output : curve.Equation outX outY,
      WeierstrassCurve.Affine.Point.mk input + WeierstrassCurve.Affine.Point.mk input =
        WeierstrassCurve.Affine.Point.mk output := by
  have nonvertical : y ≠ curve.negY x y := by
    intro equal
    apply nonzero
    simp only [WeierstrassCurve.Affine.negY, curve, zero_mul, sub_zero] at equal
    linear_combination equal
  have slopeValue : curve.slope x x y y = slope := by
    rw [curve.slope_of_Y_ne rfl nonvertical]
    simp only [curve, zero_mul, sub_zero, WeierstrassCurve.Affine.negY]
    rw [show y - (-y) = 2 * y by ring]
    exact ((eq_div_iff nonzero).mpr slopeRow).symm
  have xValue : curve.addX x x (curve.slope x x y y) = outX := by
    rw [slopeValue]
    simpa [WeierstrassCurve.Affine.addX, curve] using xRow.symm
  have yValue : curve.addY x x y (curve.slope x x y y) = outY := by
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, xValue, slopeValue]
    simp only [WeierstrassCurve.Affine.negY, curve, zero_mul, sub_zero]
    linear_combination -yRow
  simpa only [xValue, yValue] using
    (add_coordinates input input (fun equal => nonvertical equal.2))

theorem vertical_addition {x₁ x₂ y₁ y₂ : F}
    (left : curve.Equation x₁ y₁) (right : curve.Equation x₂ y₂)
    (same : x₁ = x₂) (opposite : y₁ = -y₂) :
    WeierstrassCurve.Affine.Point.mk left + WeierstrassCurve.Affine.Point.mk right = 0 := by
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq same
  simpa [WeierstrassCurve.Affine.negY, curve] using opposite


set_option pp.all true in
#check @add_coordinates
#print axioms add_coordinates

set_option pp.all true in
#check @secant_rows
#print axioms secant_rows

set_option pp.all true in
#check @tangent_rows
#print axioms tangent_rows

set_option pp.all true in
#check @vertical_addition
#print axioms vertical_addition
end ShielddSecurity.ConcretePointOperationRows01
