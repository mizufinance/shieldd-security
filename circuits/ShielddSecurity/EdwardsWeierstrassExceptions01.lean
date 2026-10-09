import ShielddSecurity.EdwardsWeierstrassMap01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsWeierstrassExceptions01
open EdwardsWeierstrassAlgebra01 EdwardsWeierstrassMap01
variable {F : Type} [Field F]

theorem no_square_root (d value : F) (nonzero : d ≠ 0) (nonSquare : Group.NoUnitSquare d) :
    value * value ≠ d := by
  intro square
  have valueNonzero : value ≠ 0 := by
    intro zero
    apply nonzero
    simpa [zero] using square.symm
  apply nonSquare value⁻¹
  rw [← square]
  field_simp [valueNonzero]

theorem weierstrass_plus_ne_zero (d A B X Y : F) (nonzeroD : d ≠ 0)
    (nonSquare : Group.NoUnitSquare d) (nonzeroB : B ≠ 0)
    (negative : 2 - A = -B * d) (equation : Equation A B X Y) : X + B ≠ 0 := by
  intro zero
  have coordinate : X = -B := eq_neg_of_add_eq_zero_left zero
  have square : Y * Y = B ^ 4 * d := by
    have relation := equation
    unfold Equation at relation
    rw [coordinate] at relation
    linear_combination relation - B ^ 3 * negative
  apply no_square_root d (Y / (B * B)) nonzeroD nonSquare
  field_simp [nonzeroB]
  linear_combination square

theorem weierstrass_zero_y (d imaginary A B X Y : F) (nonzeroD : d ≠ 0)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (nonzeroB : B ≠ 0) (parameterA : A * (1 + d) = 2 * (1 - d))
    (positive : A + 2 = -B) (equation : Equation A B X Y) (zeroY : Y = 0) : X = 0 := by
  have factor : X * (X * X + A * B * X + B * B) = 0 := by
    have relation := equation
    unfold Equation at relation
    rw [zeroY] at relation
    linear_combination -relation
  rcases mul_eq_zero.mp factor with zeroX | quadratic
  · exact zeroX
  · have minus : X - B ≠ 0 := by
      intro zero
      have coordinate : X = B := sub_eq_zero.mp zero
      have cube : B ^ 3 = 0 := by
        rw [coordinate] at quadratic
        linear_combination B ^ 2 * positive - quadratic
      exact (pow_ne_zero 3 nonzeroB) cube
    have polynomial : d * (X - B) ^ 2 = -(X + B) ^ 2 := by
      linear_combination (1 + d) * quadratic - B * X * parameterA
    apply False.elim
    apply no_square_root d (imaginary * (X + B) / (X - B)) nonzeroD nonSquare
    field_simp [minus]
    linear_combination (X + B) ^ 2 * imaginarySquare - polynomial

end ShielddSecurity.EdwardsWeierstrassExceptions01
