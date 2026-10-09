import ShielddSecurity.ElligatorCurve

set_option maxHeartbeats 200000

namespace ShielddSecurity.ElligatorChoice

variable {F : Type} [Field F]

theorem nonsquare_has_no_root (value root : F)
    (nonSquare : Group.NoUnitSquare value) (nonzero : value ≠ 0) :
    root * root ≠ value := by
  intro square
  have rootNonzero : root ≠ 0 := by
    intro zero
    exact nonzero (by simpa [zero] using square.symm)
  apply nonSquare root⁻¹
  calc
    value * root⁻¹ * root⁻¹ = (root * root) * (root⁻¹ * root⁻¹) := by rw [← square]; ring
    _ = (root * root⁻¹) * (root * root⁻¹) := by ring
    _ = 1 := by rw [mul_inv_cancel₀ rootNonzero]; simp

theorem quadratic_discriminant (c1 c2 x : F)
    (zero : (x + c1) * x + c2 = 0) :
    (2 * x + c1) * (2 * x + c1) = c1 * c1 - 4 * c2 := by
  calc
    _ = c1 * c1 - 4 * c2 + 4 * ((x + c1) * x + c2) := by ring
    _ = _ := by rw [zero]; ring

theorem cubic_nonzero (c1 c2 x : F)
    (xNonzero : x ≠ 0) (discriminantNonzero : c1 * c1 - 4 * c2 ≠ 0)
    (discriminantNonSquare : Group.NoUnitSquare (c1 * c1 - 4 * c2)) :
    Elligator.cubic c1 c2 x ≠ 0 := by
  intro zero
  have quadratic : (x + c1) * x + c2 = 0 :=
    (mul_eq_zero.mp zero).resolve_right xNonzero
  exact nonsquare_has_no_root (c1 * c1 - 4 * c2) (2 * x + c1)
    discriminantNonSquare discriminantNonzero (quadratic_discriminant c1 c2 x quadratic)

theorem first_cubic_nonzero (c1 c2 x tv : F)
    (c1Nonzero : c1 ≠ 0) (coordinate : (1 + tv) * x = -c1)
    (discriminantNonzero : c1 * c1 - 4 * c2 ≠ 0)
    (discriminantNonSquare : Group.NoUnitSquare (c1 * c1 - 4 * c2)) :
    Elligator.cubic c1 c2 x ≠ 0 := by
  apply cubic_nonzero c1 c2 x _ discriminantNonzero discriminantNonSquare
  intro zero
  have negated : -c1 = 0 := by simpa [zero] using coordinate.symm
  exact c1Nonzero (neg_eq_zero.mp negated)

set_option pp.all true in
#check @nonsquare_has_no_root
#print axioms nonsquare_has_no_root
set_option pp.all true in
#check @quadratic_discriminant
#print axioms quadratic_discriminant
set_option pp.all true in
#check @cubic_nonzero
#print axioms cubic_nonzero
set_option pp.all true in
#check @first_cubic_nonzero
#print axioms first_cubic_nonzero

end ShielddSecurity.ElligatorChoice
