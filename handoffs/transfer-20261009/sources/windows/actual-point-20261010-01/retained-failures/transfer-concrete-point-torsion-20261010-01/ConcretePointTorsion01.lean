import ShielddSecurity.TorsionCertifiedField01
import ShielddSecurity.AffineFibreBound01
import ShielddSecurity.DoublingKernelBound01
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTorsion01
open TorsionCertifiedField01

def curve : WeierstrassCurve.Affine F where
  a₁ := 0
  a₂ := A * B
  a₃ := 0
  a₄ := B * B
  a₆ := 0

theorem curve_discriminant : curve.Δ = 16 * B ^ 6 * (A * A - 4) := by
  unfold WeierstrassCurve.Δ WeierstrassCurve.b₂ WeierstrassCurve.b₄
    WeierstrassCurve.b₆ WeierstrassCurve.b₈ curve
  ring

theorem curve_elliptic : curve.IsElliptic := by
  have discriminantNonzero : A * A - 4 ≠ 0 := by
    intro zero
    apply discriminant_nonsquare 0
    simp [zero]
  have sixteenNonzero : (16 : F) ≠ 0 := by
    have sixteen : (16 : F) = (2 : F) ^ 4 := by ring
    rw [sixteen]
    exact pow_ne_zero _ TorsionPrimeNonsquare01.two_ne_zero
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [curve_discriminant]
  exact mul_ne_zero (mul_ne_zero sixteenNonzero (pow_ne_zero _ B_nonzero))
    discriminantNonzero

instance elliptic : curve.IsElliptic := curve_elliptic

def right (x : F) : F := x * x * x + (A * B) * x * x + (B * B) * x

theorem equation_iff (x y : F) : curve.Equation x y ↔ y * y = right x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [curve, right, zero_mul, add_zero, pow_succ, pow_zero, one_mul]
  simp only [mul_assoc]

def finiteSolutionsEquiv :
    {xy : F × F // curve.Equation xy.1 xy.2} ≃
      {xy : F × F // xy.2 * xy.2 = right xy.1} :=
  Equiv.subtypeEquivProp (by funext xy; exact propext (equation_iff xy.1 xy.2))

noncomputable instance finitePoint : Finite curve.Point :=
  Finite.of_equiv (Option {xy : F × F // curve.Equation xy.1 xy.2}) curve.pointEquiv.symm

theorem point_cardinality_bound : Nat.card curve.Point ≤ 2 * TorsionEulerInteger49.modulus + 1 := by
  rw [Nat.card_congr curve.pointEquiv, Nat.card_congr finiteSolutionsEquiv.optionCongr]
  have bound := AffineFibreBound01.projective_solution_bound right
  simpa only [F, Nat.card_eq_fintype_card, ZMod.card] using bound

theorem origin_equation : curve.Equation 0 0 := by
  simp [WeierstrassCurve.Affine.equation_zero, curve]

def torsion : curve.Point := WeierstrassCurve.Affine.Point.mk origin_equation

theorem two_torsion_cases (point : curve.Point) (killed : 2 • point = 0) :
    point = 0 ∨ point = torsion := by
  have selfNegative : point = -point := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [two_nsmul] using killed
  cases point with
  | zero => exact Or.inl rfl
  | some x y nonsingular =>
    have coordinates := WeierstrassCurve.Affine.Point.some.inj selfNegative
    have yNegative : y = -y := by
      simpa only [WeierstrassCurve.Affine.negY, curve, zero_mul, sub_zero] using
        coordinates.2
    have zeroY : y = 0 := by
      have twice : (2 : F) * y = 0 := by
        calc
          (2 : F) * y = y + y := by ring
          _ = y + -y := congrArg (fun z : F => y + z) yNegative
          _ = 0 := add_neg_cancel y
      exact (mul_eq_zero.mp twice).resolve_left TorsionPrimeNonsquare01.two_ne_zero
    have zeroX : x = 0 := TorsionCertifiedField01.zero_y_forces_zero_x x y
      ((equation_iff x y).mp nonsingular.1) zeroY
    right
    subst x
    subst y
    rfl

theorem doubling_kernel_bound :
    Nat.card (DoublingKernelBound01.multiply (J := curve.Point) 2).ker ≤ 2 := by
  classical
  letI := Fintype.ofFinite curve.Point
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let roots := Finset.univ.filter (fun point : curve.Point => 2 • point = 0)
  change roots.card ≤ 2
  have subset : roots ⊆ {0, torsion} := by
    intro point present
    rcases two_torsion_cases point (Finset.mem_filter.mp present).2 with zero | origin
    · simp [zero]
    · simp [origin]
  calc
    roots.card ≤ ({0, torsion} : Finset curve.Point).card := Finset.card_le_card subset
    _ ≤ 2 := by simpa using Finset.card_insert_le (0 : curve.Point) ({torsion} : Finset curve.Point)

theorem eight_kernel_bound :
    Nat.card (DoublingKernelBound01.multiply (J := curve.Point) 8).ker ≤ 8 :=
  DoublingKernelBound01.kernel_eight_bound doubling_kernel_bound

theorem torsion_nonzero : torsion ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

theorem torsion_doubled : 2 • torsion = 0 := by
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp [WeierstrassCurve.Affine.negY, curve]

theorem torsion_order : addOrderOf torsion = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact addOrderOf_eq_prime torsion_doubled torsion_nonzero

end ShielddSecurity.ConcretePointTorsion01

set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.curve
#print axioms ShielddSecurity.ConcretePointTorsion01.curve
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.curve_discriminant
#print axioms ShielddSecurity.ConcretePointTorsion01.curve_discriminant
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.curve_elliptic
#print axioms ShielddSecurity.ConcretePointTorsion01.curve_elliptic
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.elliptic
#print axioms ShielddSecurity.ConcretePointTorsion01.elliptic
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.right
#print axioms ShielddSecurity.ConcretePointTorsion01.right
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.equation_iff
#print axioms ShielddSecurity.ConcretePointTorsion01.equation_iff
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.finiteSolutionsEquiv
#print axioms ShielddSecurity.ConcretePointTorsion01.finiteSolutionsEquiv
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.finitePoint
#print axioms ShielddSecurity.ConcretePointTorsion01.finitePoint
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.point_cardinality_bound
#print axioms ShielddSecurity.ConcretePointTorsion01.point_cardinality_bound
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.origin_equation
#print axioms ShielddSecurity.ConcretePointTorsion01.origin_equation
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.torsion
#print axioms ShielddSecurity.ConcretePointTorsion01.torsion
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.two_torsion_cases
#print axioms ShielddSecurity.ConcretePointTorsion01.two_torsion_cases
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.doubling_kernel_bound
#print axioms ShielddSecurity.ConcretePointTorsion01.doubling_kernel_bound
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.eight_kernel_bound
#print axioms ShielddSecurity.ConcretePointTorsion01.eight_kernel_bound

set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.torsion_nonzero
#print axioms ShielddSecurity.ConcretePointTorsion01.torsion_nonzero
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.torsion_doubled
#print axioms ShielddSecurity.ConcretePointTorsion01.torsion_doubled
set_option pp.all true in
#check @ShielddSecurity.ConcretePointTorsion01.torsion_order
#print axioms ShielddSecurity.ConcretePointTorsion01.torsion_order
