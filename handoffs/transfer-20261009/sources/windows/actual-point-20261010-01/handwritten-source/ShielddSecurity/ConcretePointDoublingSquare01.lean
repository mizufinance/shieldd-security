import ShielddSecurity.ConcretePointTorsion01
import ShielddSecurity.WeierstrassDoublingSquare01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointDoublingSquare01
open TorsionCertifiedField01 ConcretePointTorsion01

theorem negative_y_iff (x y : F) : y = curve.negY x y ↔ y = 0 := by
  simp only [WeierstrassCurve.Affine.negY, curve, zero_mul, sub_zero]
  constructor
  · intro negative
    have twice : (2 : F) * y = 0 := by
      calc
        (2 : F) * y = y + y := by ring
        _ = y + -y := congrArg (fun z : F => y + z) negative
        _ = 0 := add_neg_cancel y
    exact (mul_eq_zero.mp twice).resolve_left TorsionPrimeNonsquare01.two_ne_zero
  · intro zero; simp [zero]

theorem regular_doubling_x_square (x y : F) (equation : curve.Equation x y)
    (nonzeroY : y ≠ 0) :
    ∃ root : F, root * root = curve.addX x x (curve.slope x x y y) := by
  have nonVertical : y ≠ curve.negY x y := fun equality =>
    nonzeroY ((negative_y_iff x y).mp equality)
  have denominator : (2 : F) * y ≠ 0 :=
    mul_ne_zero TorsionPrimeNonsquare01.two_ne_zero nonzeroY
  have slope : curve.slope x x y y =
      (3 * x * x + 2 * (A * B) * x + B * B) / (2 * y) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl nonVertical]
    simp only [curve, WeierstrassCurve.Affine.negY, zero_mul, sub_zero, pow_two]
    rw [show y - -y = 2 * y by ring]
    apply congrArg (fun numerator : F => numerator / (2 * y))
    ring
  have tangent : 2 * y * curve.slope x x y y =
      3 * x * x + 2 * (A * B) * x + B * B := by
    rw [slope, mul_comm (2 * y), div_mul_cancel₀ _ denominator]
  obtain ⟨root, square⟩ := WeierstrassDoublingSquare01.tangent_output_square
    (A * B) (B * B) x y (curve.slope x x y y)
    TorsionPrimeNonsquare01.two_ne_zero nonzeroY
    ((equation_iff x y).mp equation) tangent
  refine ⟨root, square.trans ?_⟩
  unfold WeierstrassCurve.Affine.addX curve
  ring

theorem double_has_square_x (point : curve.Point) (x y : F)
    (equation : curve.Equation x y)
    (doubled : 2 • point = WeierstrassCurve.Affine.Point.mk equation) :
    ∃ root : F, root * root = x := by
  cases point with
  | zero =>
    have nonzero := WeierstrassCurve.Affine.Point.some_ne_zero
      (WeierstrassCurve.Affine.equation_iff_nonsingular.mp equation)
    have zero : WeierstrassCurve.Affine.Point.mk equation = (0 : curve.Point) :=
      doubled.symm.trans (nsmul_zero 2)
    exact (nonzero zero).elim
  | some qx qy nonsingular =>
    have nonzeroY : qy ≠ 0 := by
      intro zero
      have vertical : qy = curve.negY qx qy := (negative_y_iff qx qy).mpr zero
      have killed : 2 • WeierstrassCurve.Affine.Point.some qx qy nonsingular = 0 := by
        rw [two_nsmul]
        exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq vertical
      have nonzero := WeierstrassCurve.Affine.Point.some_ne_zero
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp equation)
      exact nonzero (doubled.symm.trans killed)
    have nonVertical : qy ≠ curve.negY qx qy := fun equality =>
      nonzeroY ((negative_y_iff qx qy).mp equality)
    rw [two_nsmul, WeierstrassCurve.Affine.Point.add_of_Y_ne nonVertical] at doubled
    have coordinates := WeierstrassCurve.Affine.Point.some.inj doubled
    rw [← coordinates.1]
    exact regular_doubling_x_square qx qy nonsingular.1 nonzeroY

theorem no_half_of_nonsquare (x y : F) (equation : curve.Equation x y)
    (nonsquare : WeierstrassTwoTorsionAlgebra01.NoSquare x) (point : curve.Point) :
    2 • point ≠ WeierstrassCurve.Affine.Point.mk equation := by
  intro doubled
  obtain ⟨root, square⟩ := double_has_square_x point x y equation doubled
  exact nonsquare root square

theorem no_half_first (y : F) (equation : curve.Equation (TorsionEulerInteger49.firstX : F) y)
    (point : curve.Point) : 2 • point ≠ WeierstrassCurve.Affine.Point.mk equation :=
  no_half_of_nonsquare _ _ equation first_nonsquare point

theorem no_half_second (y : F) (equation : curve.Equation (TorsionEulerInteger49.secondX : F) y)
    (point : curve.Point) : 2 • point ≠ WeierstrassCurve.Affine.Point.mk equation :=
  no_half_of_nonsquare _ _ equation second_nonsquare point

end ShielddSecurity.ConcretePointDoublingSquare01

set_option pp.all true in
#check @ShielddSecurity.ConcretePointDoublingSquare01.negative_y_iff
#print axioms ShielddSecurity.ConcretePointDoublingSquare01.negative_y_iff
set_option pp.all true in
#check @ShielddSecurity.ConcretePointDoublingSquare01.regular_doubling_x_square
#print axioms ShielddSecurity.ConcretePointDoublingSquare01.regular_doubling_x_square
set_option pp.all true in
#check @ShielddSecurity.ConcretePointDoublingSquare01.double_has_square_x
#print axioms ShielddSecurity.ConcretePointDoublingSquare01.double_has_square_x
set_option pp.all true in
#check @ShielddSecurity.ConcretePointDoublingSquare01.no_half_of_nonsquare
#print axioms ShielddSecurity.ConcretePointDoublingSquare01.no_half_of_nonsquare
set_option pp.all true in
#check @ShielddSecurity.ConcretePointDoublingSquare01.no_half_first
#print axioms ShielddSecurity.ConcretePointDoublingSquare01.no_half_first
set_option pp.all true in
#check @ShielddSecurity.ConcretePointDoublingSquare01.no_half_second
#print axioms ShielddSecurity.ConcretePointDoublingSquare01.no_half_second
