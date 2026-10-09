import ShielddSecurity.EdwardsSecantPolynomials01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsSecantRational01
open EdwardsWeierstrassAlgebra01
variable {F : Type} [Field F]

theorem cayley_quotient_x (B D T x : F) (nonzeroD : D ≠ 0) (nonzeroMinus : D - T ≠ 0) :
    forwardX B x (T / D) = B * (D + T) / (D - T) := by
  have minus : 1 - T / D = (D - T) / D := by field_simp [nonzeroD] <;> ring
  have plus : 1 + T / D = (D + T) / D := by field_simp [nonzeroD] <;> ring
  unfold forwardX
  rw [minus, plus]
  field_simp [nonzeroD, nonzeroMinus]

theorem cayley_quotient_y (B C E D T : F)
    (nonzeroC : C ≠ 0) (nonzeroE : E ≠ 0) (nonzeroD : D ≠ 0)
    (nonzeroMinus : D - T ≠ 0) :
    forwardY B (C / E) (T / D) = B * B * E * (D + T) / ((D - T) * C) := by
  have minus : 1 - T / D = (D - T) / D := by field_simp [nonzeroD] <;> ring
  have plus : 1 + T / D = (D + T) / D := by field_simp [nonzeroD] <;> ring
  unfold forwardY
  rw [minus, plus]
  field_simp [nonzeroC, nonzeroE, nonzeroD, nonzeroMinus]

theorem secant_slope_row (B x z y w : F) (two : (2 : F) ≠ 0)
    (nonzeroX : x ≠ 0) (nonzeroZ : z ≠ 0)
    (minusY : 1 - y ≠ 0) (minusW : 1 - w ≠ 0) (differentY : y - w ≠ 0) :
    (B * (z * (1 + y) * (1 - w) - x * (1 + w) * (1 - y)) /
      (2 * x * z * (y - w))) * (forwardX B x y - forwardX B z w) =
      forwardY B x y - forwardY B z w := by
  unfold forwardX forwardY
  field_simp [two, nonzeroX, nonzeroZ, minusY, minusW, differentY]
  ring

/-- Quotient discharge is independent of the input curve polynomial certificate. -/
theorem normalized_x_row (d A B M P N H y w : F)
    (nonzeroD : 1 + d ≠ 0) (nonzeroM : M ≠ 0) (nonzeroH : H ≠ 0)
    (minusY : 1 - y ≠ 0) (minusW : 1 - w ≠ 0)
    (parameterA : A * (1 + d) = 2 * (1 - d))
    (parameterB : B * (1 + d) = -4)
    (polynomial : ((1 + d) * (P * (1 - y) * (1 - w) + 2 * (1 - y * w) * M) +
      2 * (1 - d) * M * (1 - y) * (1 - w)) * H ^ 2 +
      4 * N ^ 2 * M * (1 - y) * (1 - w) = 0) :
    P / M + A + (1 + y) / (1 - y) + (1 + w) / (1 - w) = B * (N / H) ^ 2 := by
  have scaled : (1 + d) * (P / M + A + (1 + y) / (1 - y) +
      (1 + w) / (1 - w) - B * (N / H) ^ 2) = 0 := by
    field_simp [nonzeroM, nonzeroH, minusY, minusW]
    linear_combination polynomial + M * (1 - y) * (1 - w) * H ^ 2 * parameterA -
      N ^ 2 * M * (1 - y) * (1 - w) * parameterB
  exact sub_eq_zero.mp ((mul_eq_zero.mp scaled).resolve_left nonzeroD)

theorem normalized_y_row (E P H y x N M C : F)
    (nonzeroH : H ≠ 0) (minusY : 1 - y ≠ 0) (nonzeroX : x ≠ 0)
    (nonzeroM : M ≠ 0) (nonzeroC : C ≠ 0)
    (polynomial : E * P * H * (1 - y) * x -
      N * ((1 + y) * M - P * (1 - y)) * C * x +
      (1 + y) * M * C * H = 0) :
    E * P / (M * C) = N / H * ((1 + y) / (1 - y) - P / M) -
      (1 + y) / ((1 - y) * x) := by
  field_simp [nonzeroH, minusY, nonzeroX, nonzeroM, nonzeroC]
  linear_combination polynomial


set_option pp.all true in
#check @cayley_quotient_x
#print axioms cayley_quotient_x

set_option pp.all true in
#check @cayley_quotient_y
#print axioms cayley_quotient_y

set_option pp.all true in
#check @secant_slope_row
#print axioms secant_slope_row

set_option pp.all true in
#check @normalized_x_row
#print axioms normalized_x_row

set_option pp.all true in
#check @normalized_y_row
#print axioms normalized_y_row
end ShielddSecurity.EdwardsSecantRational01
