import ShielddSecurity.Range

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.WeierstrassTwoTorsionAlgebra01

variable {F : Type} [Field F]

def NoSquare (value : F) : Prop := ∀ root : F, root * root ≠ value

/-- A nonzero square factor preserves nonsquareness. The concrete Euler
certificate for A²−4 and nonzero B remain separate obligations. -/
theorem scaled_discriminant_nonsquare (A B : F) (nonzeroB : B ≠ 0)
    (nonsquare : NoSquare (A * A - 4)) :
    NoSquare ((A * B) * (A * B) - 4 * (B * B)) := by
  intro root square
  apply nonsquare (root / B)
  apply mul_right_cancel₀ (mul_ne_zero nonzeroB nonzeroB)
  calc
    _ = ((root / B) * B) * ((root / B) * B) := by ring
    _ = root * root := by rw [div_mul_cancel₀ _ nonzeroB]
    _ = (A * B) * (A * B) - 4 * (B * B) := square
    _ = _ := by ring

/-- Completing the square excludes the nonzero X roots when Y is zero.
Binding Y=0 to two-torsion in the actual point group is a separate theorem. -/
theorem zero_y_forces_zero_x (a b x y : F)
    (equation : y * y = x * x * x + a * x * x + b * x)
    (zeroY : y = 0) (nonsquare : NoSquare (a * a - 4 * b)) : x = 0 := by
  have cubic : x * (x * x + a * x + b) = 0 := by
    calc
      _ = x * x * x + a * x * x + b * x := by ring
      _ = y * y := equation.symm
      _ = 0 := by rw [zeroY]; simp
  by_cases zeroX : x = 0
  · exact zeroX
  · have quadratic : x * x + a * x + b = 0 := (mul_eq_zero.mp cubic).resolve_left zeroX
    exfalso
    apply nonsquare (2 * x + a)
    calc
      _ = a * a - 4 * b + 4 * (x * x + a * x + b) := by ring
      _ = _ := by rw [quadratic]; ring

/-- Every Y fibre of an equation Y²=rhs contains at most a chosen root and
its negative. A finite cardinality bound needs a separate fibre-count proof. -/
theorem equal_square_cases (left right : F) (equal : left * left = right * right) :
    left = right ∨ left = -right := by
  have factored : (left - right) * (left + right) = 0 := by
    calc
      _ = left * left - right * right := by ring
      _ = 0 := by rw [equal]; simp
  rcases mul_eq_zero.mp factored with minus | plus
  · exact Or.inl (sub_eq_zero.mp minus)
  · exact Or.inr (eq_neg_of_add_eq_zero_left plus)

end ShielddSecurity.WeierstrassTwoTorsionAlgebra01

set_option pp.all true in
#check @ShielddSecurity.WeierstrassTwoTorsionAlgebra01.NoSquare
#print axioms ShielddSecurity.WeierstrassTwoTorsionAlgebra01.NoSquare
set_option pp.all true in
#check @ShielddSecurity.WeierstrassTwoTorsionAlgebra01.scaled_discriminant_nonsquare
#print axioms ShielddSecurity.WeierstrassTwoTorsionAlgebra01.scaled_discriminant_nonsquare
set_option pp.all true in
#check @ShielddSecurity.WeierstrassTwoTorsionAlgebra01.zero_y_forces_zero_x
#print axioms ShielddSecurity.WeierstrassTwoTorsionAlgebra01.zero_y_forces_zero_x
set_option pp.all true in
#check @ShielddSecurity.WeierstrassTwoTorsionAlgebra01.equal_square_cases
#print axioms ShielddSecurity.WeierstrassTwoTorsionAlgebra01.equal_square_cases
