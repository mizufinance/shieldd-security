import ShielddSecurity.EdwardsTangentPolynomials01
import ShielddSecurity.EdwardsSecantRational01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsTangentRational01
variable {F : Type} [Field F]

theorem normalized_tangent_slope (d A B x y K : F) (nonzeroD : 1 + d ≠ 0)
    (parameterA : A * (1 + d) = 2 * (1 - d)) (parameterB : B * (1 + d) = -4)
    (polynomial : 4 * K * (1 - y * y) + x ^ 2 *
      ((1 + d) * (3 * (1 + y) ^ 2 + (1 - y) ^ 2) +
        4 * (1 - d) * (1 - y * y)) = 0) :
    B * K * (1 + y) * (1 - y) = x ^ 2 *
      (3 * (1 + y) ^ 2 + 2 * A * (1 + y) * (1 - y) + (1 - y) ^ 2) := by
  have scaled : (1 + d) * (B * K * (1 + y) * (1 - y) - x ^ 2 *
      (3 * (1 + y) ^ 2 + 2 * A * (1 + y) * (1 - y) + (1 - y) ^ 2)) = 0 := by
    linear_combination -polynomial + K * (1 + y) * (1 - y) * parameterB -
      2 * x ^ 2 * (1 + y) * (1 - y) * parameterA
  exact sub_eq_zero.mp ((mul_eq_zero.mp scaled).resolve_left nonzeroD)


set_option pp.all true in
#check @normalized_tangent_slope
#print axioms normalized_tangent_slope
end ShielddSecurity.EdwardsTangentRational01
