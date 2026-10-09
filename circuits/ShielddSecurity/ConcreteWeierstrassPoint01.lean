import ShielddSecurity.ConcreteEdwardsParameters01
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteWeierstrassPoint01
open ConcreteJubjubField01 ConcreteEdwardsParameters01

/-- The concrete affine equation, over the kernel-certified prime field. -/
def curve : WeierstrassCurve.Affine F where
  a₁ := 0
  a₂ := A * B
  a₃ := 0
  a₄ := B * B
  a₆ := 0

theorem curve_discriminant : curve.Δ = discriminant := by
  unfold WeierstrassCurve.Δ WeierstrassCurve.b₂ WeierstrassCurve.b₄
    WeierstrassCurve.b₆ WeierstrassCurve.b₈ curve discriminant
  ring

theorem curve_discriminant_nonzero : curve.Δ ≠ 0 := by
  rw [curve_discriminant]
  exact discriminant_nonzero

theorem curve_elliptic : curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr curve_discriminant_nonzero⟩

instance : curve.IsElliptic := curve_elliptic

theorem equation_iff (x y : F) :
    EdwardsWeierstrassAlgebra01.Equation A B x y ↔ curve.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [curve, zero_mul, add_zero, pow_succ, pow_zero, one_mul]
  unfold EdwardsWeierstrassAlgebra01.Equation
  simp only [mul_assoc]

def finiteSolutionsEquiv :
    {point : Group.Point F // EdwardsWeierstrassAlgebra01.Equation A B point.x point.y} ≃
      {xy : F × F // curve.Equation xy.fst xy.snd} where
  toFun point := ⟨(point.val.x, point.val.y), (equation_iff _ _).mp point.property⟩
  invFun point := ⟨⟨point.val.fst, point.val.snd⟩, (equation_iff _ _).mpr point.property⟩
  left_inv point := by rcases point with ⟨⟨x, y⟩, h⟩; rfl
  right_inv point := by rcases point with ⟨⟨x, y⟩, h⟩; rfl

/-- A bijection of the full point sets. Addition compatibility remains a separate obligation. -/
noncomputable def equivalence : EdwardsWeierstrassEquiv01.Edwards parameters ≃ curve.Point :=
  (EdwardsWeierstrassEquiv01.equivalence parameters).trans
    (finiteSolutionsEquiv.optionCongr.trans curve.pointEquiv.symm)

theorem equivalence_identity :
    equivalence (EdwardsWeierstrassEquiv01.identity parameters) = 0 := by
  change curve.pointEquiv.symm
    (finiteSolutionsEquiv.optionCongr
      (EdwardsWeierstrassEquiv01.forward parameters
        (EdwardsWeierstrassEquiv01.identity parameters))) = 0
  rw [EdwardsWeierstrassEquiv01.forward_identity]
  exact curve.pointEquiv_symm_none

theorem origin_equation : curve.Equation 0 0 := by
  simp [WeierstrassCurve.Affine.equation_zero, curve]

theorem equivalence_torsion :
    equivalence (EdwardsWeierstrassEquiv01.torsion parameters) =
      WeierstrassCurve.Affine.Point.mk origin_equation := by
  change curve.pointEquiv.symm
    (finiteSolutionsEquiv.optionCongr
      (EdwardsWeierstrassEquiv01.forward parameters
        (EdwardsWeierstrassEquiv01.torsion parameters))) = _
  rw [EdwardsWeierstrassEquiv01.forward_torsion]
  exact curve.pointEquiv_symm_some origin_equation

end ShielddSecurity.ConcreteWeierstrassPoint01
