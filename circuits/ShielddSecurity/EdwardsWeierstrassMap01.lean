import ShielddSecurity.EdwardsWeierstrassAlgebra01
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsWeierstrassMap01
open EdwardsWeierstrassAlgebra01
variable {F : Type} [Field F]

theorem scaled_parameter (d A B : F) (two : (2 : F) ≠ 0)
    (parameterA : A * (1 + d) = 2 * (1 - d))
    (parameterB : B * (1 + d) = -4) : 2 * A = B * (d - 1) := by
  apply mul_left_cancel₀ two
  linear_combination A * parameterB - B * parameterA

theorem parameter_plus (d A B : F) (two : (2 : F) ≠ 0)
    (parameterB : B * (1 + d) = -4) (scaled : 2 * A = B * (d - 1)) :
    A + 2 = -B := by
  apply mul_left_cancel₀ two
  linear_combination parameterB + scaled

theorem parameter_minus (d A B : F) (two : (2 : F) ≠ 0)
    (parameterB : B * (1 + d) = -4) (scaled : 2 * A = B * (d - 1)) :
    2 - A = -B * d := by
  apply mul_left_cancel₀ two
  linear_combination parameterB - scaled

theorem forward_curve_polynomial (d A B x y : F)
    (positive : A + 2 = -B) (negative : 2 - A = -B * d)
    (equation : Group.OnCurve d ⟨x, y⟩) :
    B * (1 + y) ^ 2 * (1 - y) - x ^ 2 *
      ((1 + y) ^ 3 + A * (1 + y) ^ 2 * (1 - y) + (1 + y) * (1 - y) ^ 2) = 0 := by
  have residual : y * y - x * x - 1 - d * x * x * y * y = 0 := by
    unfold Group.OnCurve at equation
    linear_combination equation
  calc
    _ = (1 + y) * (B * (1 - y * y) - x * x * ((A + 2) + (2 - A) * y * y)) := by ring
    _ = -B * (1 + y) * (y * y - x * x - 1 - d * x * x * y * y) := by
      rw [positive, negative]
      ring
    _ = 0 := by rw [residual]; ring

theorem forward_on_curve (d A B x y : F) (nonzeroX : x ≠ 0) (minus : 1 - y ≠ 0)
    (positive : A + 2 = -B) (negative : 2 - A = -B * d)
    (equation : Group.OnCurve d ⟨x, y⟩) :
    Equation A B (forwardX B x y) (forwardY B x y) := by
  have polynomial := forward_curve_polynomial d A B x y positive negative equation
  unfold Equation forwardX forwardY
  field_simp [nonzeroX, minus]
  linear_combination B ^ 3 * polynomial

theorem forward_plus (B x y : F) (minus : 1 - y ≠ 0) :
    forwardX B x y + B = 2 * B / (1 - y) := by
  unfold forwardX
  field_simp
  ring

theorem inverse_minus (B X : F) (plus : X + B ≠ 0) :
    1 - inverseY B X = 2 * B / (X + B) := by
  unfold inverseY
  field_simp
  ring

theorem inverse_plus (B X : F) (plus : X + B ≠ 0) :
    1 + inverseY B X = 2 * X / (X + B) := by
  unfold inverseY
  field_simp
  ring

theorem inverse_curve_polynomial (d A B X Y : F)
    (parameterB : B * (1 + d) = -4) (scaled : 2 * A = B * (d - 1))
    (equation : Equation A B X Y) :
    (X - B) ^ 2 * Y ^ 2 - B ^ 2 * X ^ 2 * (X + B) ^ 2 -
      (X + B) ^ 2 * Y ^ 2 - d * B ^ 2 * X ^ 2 * (X - B) ^ 2 = 0 := by
  unfold Equation at equation
  linear_combination -4 * B * X * equation - B * X ^ 2 * (X ^ 2 + B ^ 2) * parameterB -
    2 * B ^ 2 * X ^ 3 * scaled

theorem inverse_on_curve (d A B X Y : F) (nonzeroY : Y ≠ 0) (plus : X + B ≠ 0)
    (parameterB : B * (1 + d) = -4) (scaled : 2 * A = B * (d - 1))
    (equation : Equation A B X Y) :
    Group.OnCurve d ⟨inverseX B X Y, inverseY B X⟩ := by
  have polynomial := inverse_curve_polynomial d A B X Y parameterB scaled equation
  unfold Group.OnCurve inverseX inverseY
  field_simp [nonzeroY, plus]
  linear_combination polynomial

theorem forward_inverse_x (B x y : F) (nonzeroB : B ≠ 0)
    (nonzeroX : x ≠ 0) (minus : 1 - y ≠ 0) (plus : 1 + y ≠ 0) :
    inverseX B (forwardX B x y) (forwardY B x y) = x := by
  unfold inverseX forwardX forwardY
  field_simp [nonzeroB, nonzeroX, minus, plus]

theorem cancel_scaled_coordinate (B X : F) (two : (2 : F) ≠ 0) (nonzeroB : B ≠ 0) :
    B * (X + B + (X - B)) / (X + B - (X - B)) = X := by
  rw [show X + B + (X - B) = 2 * X by ring,
      show X + B - (X - B) = 2 * B by ring]
  apply (div_eq_iff (mul_ne_zero two nonzeroB)).mpr
  ring

theorem forward_inverse_y (B x y : F) (two : (2 : F) ≠ 0)
    (nonzeroB : B ≠ 0) (minus : 1 - y ≠ 0) :
    inverseY B (forwardX B x y) = y := by
  have denominator : forwardX B x y + B ≠ 0 := by
    rw [forward_plus B x y minus]
    exact div_ne_zero (mul_ne_zero two nonzeroB) minus
  unfold inverseY forwardX
  field_simp [two, nonzeroB, minus, denominator]
  rw [show 1 + y - (1 - y) = 2 * y by ring,
      show 1 + y + (1 - y) = (2 : F) by ring]
  apply (div_eq_iff two).mpr
  ring

theorem inverse_forward_x (B X Y : F) (two : (2 : F) ≠ 0)
    (nonzeroB : B ≠ 0) (nonzeroY : Y ≠ 0) (plus : X + B ≠ 0) :
    forwardX B (inverseX B X Y) (inverseY B X) = X := by
  have denominator : 1 - inverseY B X ≠ 0 := by
    rw [inverse_minus B X plus]
    exact div_ne_zero (mul_ne_zero two nonzeroB) plus
  unfold forwardX inverseY
  field_simp [two, nonzeroB, plus, denominator]
  exact cancel_scaled_coordinate B X two nonzeroB

theorem inverse_forward_y (B X Y : F) (two : (2 : F) ≠ 0)
    (nonzeroB : B ≠ 0) (nonzeroX : X ≠ 0) (nonzeroY : Y ≠ 0) (plus : X + B ≠ 0) :
    forwardY B (inverseX B X Y) (inverseY B X) = Y := by
  have denominator : 1 - inverseY B X ≠ 0 := by
    rw [inverse_minus B X plus]
    exact div_ne_zero (mul_ne_zero two nonzeroB) plus
  unfold forwardY inverseX inverseY
  field_simp [two, nonzeroB, nonzeroX, nonzeroY, plus, denominator]
  exact cancel_scaled_coordinate B X two nonzeroB

end ShielddSecurity.EdwardsWeierstrassMap01
