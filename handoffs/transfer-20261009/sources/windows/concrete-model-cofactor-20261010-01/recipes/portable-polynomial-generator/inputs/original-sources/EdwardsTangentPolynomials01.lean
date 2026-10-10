import ShielddSecurity.EdwardsWeierstrassEquiv01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsTangentPolynomials01
variable {F : Type} [Field F]

theorem tangent_slope_polynomial (d x y : F)
    (input : y * y - x * x = 1 + d * x * x * y * y) :
    let delta := d * x * x * y * y
    let diagonal := y * y + x * x
    let cross := 2 * x * y
    let m := 1 - delta - diagonal
    let p := 1 - delta + diagonal
    let k := 2 + y - d * x * x * y
    let h := 2 * x
    4 * k * (1 - y * y) + x ^ 2 *
      ((1 + d) * (3 * (1 + y) ^ 2 + (1 - y) ^ 2) +
        4 * (1 - d) * (1 - y * y)) = 0 := by
  dsimp only
  linear_combination -(4 * (2 + y)) * input

theorem tangent_x_polynomial (d x y : F)
    (input : y * y - x * x = 1 + d * x * x * y * y) :
    let delta := d * x * x * y * y
    let diagonal := y * y + x * x
    let cross := 2 * x * y
    let m := 1 - delta - diagonal
    let p := 1 - delta + diagonal
    let k := 2 + y - d * x * x * y
    let h := 2 * x
    ((1 + d) * (p * (1 - y) + 2 * (1 + y) * m) +
      2 * (1 - d) * m * (1 - y)) * h ^ 2 + 4 * k ^ 2 * m * (1 - y) = 0 := by
  dsimp only
  linear_combination -(4 * (4 + ((-1) * (y ^ 3)) + ((-3) * (x ^ 2)) + ((-3) * (y ^ 2)) + (d * (x ^ 2)) + ((-1) * y * (x ^ 2)) + ((d ^ 2) * (x ^ 4) * (y ^ 3)) + ((-1) * d * y * (x ^ 2)) + ((-1) * (d ^ 2) * (x ^ 4) * (y ^ 2)) + ((-4) * d * (x ^ 2) * (y ^ 2)))) * input

theorem tangent_y_polynomial (d x y : F)
    (input : y * y - x * x = 1 + d * x * x * y * y) :
    let delta := d * x * x * y * y
    let diagonal := y * y + x * x
    let cross := 2 * x * y
    let m := 1 - delta - diagonal
    let p := 1 - delta + diagonal
    let k := 2 + y - d * x * x * y
    let h := 2 * x
    (1 + delta) * p * h * (1 - y) * x -
      k * ((1 + y) * m - p * (1 - y)) * cross * x +
      (1 + y) * m * cross * h = 0 := by
  dsimp only
  linear_combination -((-2) * (x ^ 2) * (1 + y) * ((-1) + (d * (x ^ 2) * (y ^ 2)))) * input

end ShielddSecurity.EdwardsTangentPolynomials01
