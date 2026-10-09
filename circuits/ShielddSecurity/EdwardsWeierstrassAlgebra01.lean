import ShielddSecurity.Group

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsWeierstrassAlgebra01
variable {F : Type} [Field F]

def Equation (A B X Y : F) : Prop := Y * Y = X * X * X + A * B * X * X + B * B * X

def forwardX (B x y : F) : F := B * (1 + y) / (1 - y)
def forwardY (B x y : F) : F := B * B * (1 + y) / ((1 - y) * x)
def inverseX (B X Y : F) : F := B * X / Y
def inverseY (B X : F) : F := (X - B) / (X + B)

theorem coefficient_ne_neg_one (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) : d ≠ -1 := by
  intro equal
  apply nonSquare imaginary
  rw [equal, neg_one_mul, neg_mul, imaginarySquare]
  ring

theorem one_add_coefficient_ne_zero (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) : 1 + d ≠ 0 := by
  intro zero
  exact coefficient_ne_neg_one d imaginary nonSquare imaginarySquare (eq_neg_of_add_eq_zero_right zero)

theorem parameterB_ne_zero (d B : F) (two : (2 : F) ≠ 0)
    (parameterB : B * (1 + d) = -4) : B ≠ 0 := by
  intro zero
  have four : (4 : F) ≠ 0 := by
    have product := mul_ne_zero two two
    convert product using 1 <;> ring
  apply four
  have negative : -(4 : F) = 0 := by simpa [zero] using parameterB.symm
  exact neg_eq_zero.mp negative

theorem edwards_zero_x (d : F) (point : Group.Point F) (onCurve : Group.OnCurve d point)
    (zero : point.x = 0) : point.y = 1 ∨ point.y = -1 := by
  have square : point.y * point.y = 1 := by simpa [Group.OnCurve, zero] using onCurve
  have factors : (point.y - 1) * (point.y + 1) = 0 := by
    calc
      _ = point.y * point.y - 1 := by ring
      _ = 0 := by rw [square]; ring
  rcases mul_eq_zero.mp factors with positive | negative
  · exact Or.inl (sub_eq_zero.mp positive)
  · exact Or.inr (eq_neg_of_add_eq_zero_left negative)

theorem edwards_one_y (d : F) (point : Group.Point F) (onCurve : Group.OnCurve d point)
    (coefficient : 1 + d ≠ 0) (one : point.y = 1) : point.x = 0 := by
  have factors : (1 + d) * (point.x * point.x) = 0 := by
    have equation := onCurve
    simp only [Group.OnCurve, one, mul_one] at equation
    calc
      _ = -(1 - point.x * point.x - (1 + d * point.x * point.x)) := by ring
      _ = 0 := by rw [equation]; ring
  rcases mul_eq_zero.mp factors with impossible | square
  · exact False.elim (coefficient impossible)
  · exact (mul_self_eq_zero.mp square)

theorem edwards_neg_one_y (d : F) (point : Group.Point F) (onCurve : Group.OnCurve d point)
    (coefficient : 1 + d ≠ 0) (one : point.y = -1) : point.x = 0 := by
  have factors : (1 + d) * (point.x * point.x) = 0 := by
    have equation := onCurve
    simp only [Group.OnCurve, one, mul_neg, neg_mul, mul_one, neg_neg] at equation
    calc
      _ = -(1 - point.x * point.x - (1 + d * point.x * point.x)) := by ring
      _ = 0 := by rw [equation]; ring
  rcases mul_eq_zero.mp factors with impossible | square
  · exact False.elim (coefficient impossible)
  · exact (mul_self_eq_zero.mp square)

theorem weierstrass_origin (A B : F) : Equation A B 0 0 := by simp [Equation]

theorem forwardX_neg (B x y : F) : forwardX B (-x) y = forwardX B x y := rfl

theorem forwardY_neg (B x y : F) : forwardY B (-x) y = -(forwardY B x y) := by
  simp [forwardY, mul_neg, div_neg]

theorem inverseX_neg (B X Y : F) : inverseX B X (-Y) = -(inverseX B X Y) := by
  simp [inverseX, div_neg]

end ShielddSecurity.EdwardsWeierstrassAlgebra01
