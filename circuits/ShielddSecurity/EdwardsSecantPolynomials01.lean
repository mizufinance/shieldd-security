import ShielddSecurity.EdwardsWeierstrassEquiv01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsSecantPolynomials01
variable {F : Type} [Field F]

/-- Generated symbolic certificate from the two input curve equations.
The generator proposes coefficients; Lean checks each polynomial identity. -/
theorem curve_interaction (d x z y w : F)
    (left : y * y - x * x = 1 + d * x * x * y * y)
    (right : w * w - z * z = 1 + d * z * z * w * w) :
    -w ^ 2 * x ^ 2 * y ^ 2 - w ^ 2 * x ^ 2 * z ^ 2 +
      w ^ 2 * y ^ 2 * z ^ 2 - w ^ 2 * z ^ 2 +
      x ^ 2 * y ^ 2 * z ^ 2 + x ^ 2 * y ^ 2 = 0 := by
  linear_combination z ^ 2 * w ^ 2 * left - x ^ 2 * y ^ 2 * right

theorem secant_y_polynomial (d x z y w : F)
    (left : y * y - x * x = 1 + d * x * x * y * y)
    (right : w * w - z * z = 1 + d * z * z * w * w) :
    let delta := d * x * z * y * w
    let diagonal := y * w + x * z
    let cross := x * w + y * z
    let m := 1 - delta - diagonal
    let p := 1 - delta + diagonal
    let n := z * (1 + y) * (1 - w) - x * (1 + w) * (1 - y)
    let h := 2 * x * z * (y - w)
    (1 + delta) * p * h * (1 - y) * x -
      n * ((1 + y) * m - p * (1 - y)) * cross * x +
      (1 + y) * m * cross * h = 0 := by
  have mixed := curve_interaction d x z y w left right
  dsimp only
  linear_combination -(2 * w * z * (((w ^ 2) * (z ^ 2)) + ((x ^ 2) * (z ^ 2)) + ((-1) * w * (x ^ 2)) + ((-1) * (w ^ 2) * (x ^ 2)) + (w * y * (x ^ 2)) + (x * z * (y ^ 2)) + (y * (w ^ 2) * (x ^ 2)) + ((-1) * w * y * (z ^ 2)) + ((-1) * x * y * z) + ((-1) * x * z * (w ^ 2)) + ((-1) * y * (w ^ 2) * (z ^ 2)) + ((-1) * y * (x ^ 2) * (z ^ 2)) + (d * (w ^ 2) * (x ^ 2) * (z ^ 2)) + (d * w * (x ^ 2) * (y ^ 2) * (z ^ 2)) + ((-1) * d * w * y * (x ^ 2) * (z ^ 2)) + ((-1) * d * y * (w ^ 2) * (x ^ 2) * (z ^ 2)))) * left - (2 * (x ^ 2) * ((y * z) + ((-1) * w * z) + (w * x * y) + (w * y * z) + ((-1) * w * z * (x ^ 2)) + (w * y * z * (x ^ 2)))) * right + ((-2) * ((w * x) + (y * z) + ((-1) * w * z) + (w * y * z))) * mixed

theorem secant_x_polynomial (d x z y w : F)
    (left : y * y - x * x = 1 + d * x * x * y * y)
    (right : w * w - z * z = 1 + d * z * z * w * w) :
    let delta := d * x * z * y * w
    let diagonal := y * w + x * z
    let cross := x * w + y * z
    let m := 1 - delta - diagonal
    let p := 1 - delta + diagonal
    let n := z * (1 + y) * (1 - w) - x * (1 + w) * (1 - y)
    let h := 2 * x * z * (y - w)
    ((1 + d) * (p * (1 - y) * (1 - w) + 2 * (1 - y * w) * m) +
      2 * (1 - d) * m * (1 - y) * (1 - w)) * h ^ 2 +
      4 * n ^ 2 * m * (1 - y) * (1 - w) = 0 := by
  have mixed := curve_interaction d x z y w left right
  dsimp only
  linear_combination -(4 * z * (z + (x * (z ^ 2)) + (y * z) + ((-3) * w * z) + ((-3) * x * (w ^ 3)) + ((-3) * x * (w ^ 4)) + (3 * w * x) + (3 * x * (w ^ 2)) + (3 * z * (w ^ 4)) + (5 * z * (w ^ 3)) + (6 * z * (w ^ 2)) + (w * x * (y ^ 2)) + (x * (w ^ 2) * (y ^ 2)) + ((-1) * w * z * (y ^ 2)) + ((-1) * x * (w ^ 3) * (y ^ 2)) + ((-1) * x * (w ^ 4) * (y ^ 2)) + ((-1) * x * (w ^ 4) * (z ^ 2)) + ((-8) * y * z * (w ^ 3)) + ((-4) * w * y * z) + ((-3) * w * x * y) + ((-3) * x * y * (w ^ 2)) + ((-3) * x * y * (z ^ 2)) + ((-3) * x * (w ^ 2) * (z ^ 2)) + ((-3) * x * (w ^ 3) * (z ^ 2)) + ((-2) * y * z * (w ^ 4)) + ((-2) * z * (w ^ 3) * (y ^ 2)) + (2 * z * (w ^ 4) * (y ^ 2)) + (3 * x * y * (w ^ 3)) + (3 * x * y * (w ^ 4)) + (3 * z * (w ^ 2) * (y ^ 2)) + (4 * w * x * (z ^ 2)) + (5 * y * z * (w ^ 2)) + (d * x * (w ^ 3) * (z ^ 2)) + ((-1) * x * (w ^ 2) * (y ^ 2) * (z ^ 2)) + ((-3) * x * y * (w ^ 2) * (z ^ 2)) + (2 * d * x * (w ^ 2) * (z ^ 2)) + (2 * x * y * (w ^ 3) * (z ^ 2)) + (3 * d * x * (w ^ 4) * (z ^ 2)) + (3 * w * x * (y ^ 2) * (z ^ 2)) + (d * x * y * (w ^ 2) * (z ^ 2)) + ((-1) * d * w * x * y * (z ^ 2)) + ((-1) * d * w * x * (y ^ 2) * (z ^ 2)) + ((-6) * d * x * y * (w ^ 3) * (z ^ 2)) + (3 * d * x * (w ^ 2) * (y ^ 2) * (z ^ 2)))) * left - ((-4) * x * (((-1) * x) + (2 * z) + (w * z) + (z * (x ^ 2)) + ((-1) * w * x) + ((-2) * y * z) + ((-2) * z * (y ^ 2)) + (2 * z * (y ^ 3)) + (3 * x * y) + (3 * z * (w ^ 2)) + (x * y * (w ^ 2)) + (z * (w ^ 2) * (y ^ 3)) + (z * (w ^ 2) * (y ^ 4)) + ((-1) * y * z * (w ^ 2)) + ((-4) * z * (w ^ 2) * (y ^ 2)) + ((-3) * w * y * z) + ((-3) * w * z * (y ^ 4)) + ((-3) * y * z * (x ^ 2)) + (2 * w * z * (y ^ 2)) + (3 * w * z * (y ^ 3)) + (3 * z * (w ^ 2) * (x ^ 2)) + (4 * w * x * y) + (4 * w * z * (x ^ 2)) + ((-6) * w * y * z * (x ^ 2)) + ((-3) * y * z * (w ^ 2) * (x ^ 2)) + (d * w * y * z * (x ^ 2)) + (d * y * z * (w ^ 2) * (x ^ 2)))) * right + (4 * (1 + w) * (3 + ((-1) * y) + (3 * w) + (w * (y ^ 2)) + ((-3) * w * y) + ((-3) * x * z) + (x * y * z) + ((-1) * w * x * z))) * mixed

end ShielddSecurity.EdwardsSecantPolynomials01
