import ShielddSecurity.EdwardsWeierstrassExceptions01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsWeierstrassEquiv01
open EdwardsWeierstrassAlgebra01 EdwardsWeierstrassMap01 EdwardsWeierstrassExceptions01
variable {F : Type} [Field F]

/-- Algebraic parameters, without a group law, cardinality or native representation contract. -/
structure Parameters (F : Type) [Field F] where
  d : F
  imaginary : F
  A : F
  B : F
  two : (2 : F) ≠ 0
  nonzeroD : d ≠ 0
  nonSquare : Group.NoUnitSquare d
  imaginarySquare : imaginary * imaginary = -1
  parameterA : A * (1 + d) = 2 * (1 - d)
  parameterB : B * (1 + d) = -4

variable (params : Parameters F)
abbrev Edwards := {point : Group.Point F // Group.OnCurve params.d point}
/-- All affine solutions of the displayed Weierstrass equation, plus infinity.
The join to Mathlib's nonsingular Point type is a separate obligation. -/
abbrev RationalWeierstrass := Option {point : Group.Point F // Equation params.A params.B point.x point.y}

theorem point_ext {left right : Group.Point F} (x : left.x = right.x) (y : left.y = right.y) :
    left = right := by cases left; cases right; simp_all

theorem nonzeroB : params.B ≠ 0 := parameterB_ne_zero params.d params.B params.two params.parameterB
theorem oneAdd : 1 + params.d ≠ 0 :=
  one_add_coefficient_ne_zero params.d params.imaginary params.nonSquare params.imaginarySquare
theorem scaled : 2 * params.A = params.B * (params.d - 1) :=
  scaled_parameter params.d params.A params.B params.two params.parameterA params.parameterB
theorem positive : params.A + 2 = -params.B :=
  parameter_plus params.d params.A params.B params.two params.parameterB (scaled params)
theorem negative : 2 - params.A = -params.B * params.d :=
  parameter_minus params.d params.A params.B params.two params.parameterB (scaled params)

def identity : Edwards params := ⟨⟨0, 1⟩, by simp [Group.OnCurve]⟩
def torsion : Edwards params := ⟨⟨0, -1⟩, by simp [Group.OnCurve]⟩
def origin : RationalWeierstrass params := some ⟨⟨0, 0⟩, weierstrass_origin _ _⟩

noncomputable def forward (point : Edwards params) : RationalWeierstrass params := by
  classical
  exact if one : point.val.y = 1 then none else
    if zero : point.val.x = 0 then origin params else
      some ⟨⟨forwardX params.B point.val.x point.val.y, forwardY params.B point.val.x point.val.y⟩,
        forward_on_curve params.d params.A params.B point.val.x point.val.y zero
          (fun equal => one (sub_eq_zero.mp equal).symm)
          (positive params) (negative params) point.property⟩

noncomputable def backward (point : RationalWeierstrass params) : Edwards params := by
  classical
  exact match point with
  | none => identity params
  | some point => if zero : point.val.y = 0 then torsion params else
      ⟨⟨inverseX params.B point.val.x point.val.y, inverseY params.B point.val.x⟩,
        inverse_on_curve params.d params.A params.B point.val.x point.val.y zero
          (weierstrass_plus_ne_zero params.d params.A params.B point.val.x point.val.y
            params.nonzeroD params.nonSquare (nonzeroB params) (negative params) point.property)
          params.parameterB (scaled params) point.property⟩

theorem negOne (params : Parameters F) : (-1 : F) ≠ 1 := by
  intro equal
  apply params.two
  linear_combination -equal

theorem backward_forward (point : Edwards params) : backward params (forward params point) = point := by
  classical
  rcases point with ⟨⟨x, y⟩, curve⟩
  by_cases one : y = 1
  · have zero := edwards_one_y params.d ⟨x, y⟩ curve (oneAdd params) one
    dsimp at zero
    subst x; subst y
    simp [forward, backward, identity]
  · by_cases zero : x = 0
    · have sign := edwards_zero_x params.d ⟨x, y⟩ curve zero
      dsimp at sign
      have minusOne : y = -1 := sign.resolve_left one
      subst x; subst y
      simp [forward, backward, origin, torsion, negOne params]
    · have minus : 1 - y ≠ 0 := fun equal => one (sub_eq_zero.mp equal).symm
      have plus : 1 + y ≠ 0 := by
        intro equal
        have minusOne : y = -1 := eq_neg_of_add_eq_zero_right equal
        exact zero (edwards_neg_one_y params.d ⟨x, y⟩ curve (oneAdd params) minusOne)
      have nonzeroY : forwardY params.B x y ≠ 0 := by
        unfold forwardY
        exact div_ne_zero (mul_ne_zero (mul_ne_zero (nonzeroB params) (nonzeroB params)) plus)
          (mul_ne_zero minus zero)
      apply Subtype.ext
      apply point_ext
      · simpa [forward, backward, one, zero, nonzeroY] using
          forward_inverse_x params.B x y (nonzeroB params) zero minus plus
      · simpa [forward, backward, one, zero, nonzeroY] using
          forward_inverse_y params.B x y params.two (nonzeroB params) minus

theorem forward_backward (point : RationalWeierstrass params) : forward params (backward params point) = point := by
  classical
  cases point with
  | none => simp [backward, forward, identity]
  | some point =>
    rcases point with ⟨⟨X, Y⟩, equation⟩
    by_cases zero : Y = 0
    · have zeroX := weierstrass_zero_y params.d params.imaginary params.A params.B X Y
        params.nonzeroD params.nonSquare params.imaginarySquare (nonzeroB params)
        params.parameterA (positive params) equation zero
      subst X; subst Y
      simp [backward, forward, torsion, origin, negOne params]
    · have plus := weierstrass_plus_ne_zero params.d params.A params.B X Y
        params.nonzeroD params.nonSquare (nonzeroB params) (negative params) equation
      have zeroX : X ≠ 0 := by
        intro equal
        have square : Y * Y = 0 := by simpa [Equation, equal] using equation
        exact zero (mul_self_eq_zero.mp square)
      have inverseNonzero : inverseX params.B X Y ≠ 0 := by
        unfold inverseX
        exact div_ne_zero (mul_ne_zero (nonzeroB params) zeroX) zero
      have inverseNotOne : inverseY params.B X ≠ 1 := by
        intro equal
        have difference : 1 - inverseY params.B X ≠ 0 := by
          rw [inverse_minus params.B X plus]
          exact div_ne_zero (mul_ne_zero params.two (nonzeroB params)) plus
        apply difference
        rw [equal]; ring
      simp only [backward, dif_neg zero, forward, dif_neg inverseNotOne, dif_neg inverseNonzero]
      apply congrArg some
      apply Subtype.ext
      apply point_ext
      · exact inverse_forward_x params.B X Y params.two (nonzeroB params) zero plus
      · exact inverse_forward_y params.B X Y params.two (nonzeroB params) zeroX zero plus

noncomputable def equivalence : Edwards params ≃ RationalWeierstrass params where
  toFun := forward params
  invFun := backward params
  left_inv := backward_forward params
  right_inv := forward_backward params

def edwardsNeg (point : Edwards params) : Edwards params :=
  ⟨⟨-point.val.x, point.val.y⟩, by simpa [Group.OnCurve] using point.property⟩

def weierstrassNeg : RationalWeierstrass params → RationalWeierstrass params
  | none => none
  | some point => some ⟨⟨point.val.x, -point.val.y⟩, by simpa [Equation] using point.property⟩

theorem forward_identity : forward params (identity params) = none := by
  simp [forward, identity]

theorem forward_torsion : forward params (torsion params) = origin params := by
  simp [forward, torsion, negOne params]

theorem forward_neg (point : Edwards params) :
    forward params (edwardsNeg params point) = weierstrassNeg params (forward params point) := by
  classical
  by_cases one : point.val.y = 1
  · simp [forward, edwardsNeg, weierstrassNeg, one]
  · by_cases zero : point.val.x = 0
    · simp [forward, edwardsNeg, weierstrassNeg, one, zero, origin]
    · have nonzero : -point.val.x ≠ 0 := neg_ne_zero.mpr zero
      simp [forward, edwardsNeg, weierstrassNeg, one, zero, nonzero, forwardX_neg, forwardY_neg]

theorem backward_neg (point : RationalWeierstrass params) :
    backward params (weierstrassNeg params point) = edwardsNeg params (backward params point) := by
  apply (equivalence params).injective
  change forward params (backward params (weierstrassNeg params point)) =
    forward params (edwardsNeg params (backward params point))
  rw [forward_backward, forward_neg, forward_backward]

end ShielddSecurity.EdwardsWeierstrassEquiv01
