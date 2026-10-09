import ShielddSecurity.ConcreteWeierstrassPoint01
import ShielddSecurity.EdwardsAdditionPilot01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointAdditionPilot01
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01

noncomputable def rationalEquivalence :
    EdwardsWeierstrassEquiv01.RationalWeierstrass parameters ≃ curve.Point :=
  finiteSolutionsEquiv.optionCongr.trans curve.pointEquiv.symm

theorem rational_none : rationalEquivalence none = 0 := curve.pointEquiv_symm_none

theorem rational_some (point :
    {point : Group.Point F // EdwardsWeierstrassAlgebra01.Equation A B point.x point.y}) :
    rationalEquivalence (some point) =
      WeierstrassCurve.Affine.Point.mk ((equation_iff _ _).mp point.property) :=
  curve.pointEquiv_symm_some _

theorem mk_neg {x y : F} (valid : curve.Equation x y) (negValid : curve.Equation x (-y)) :
    WeierstrassCurve.Affine.Point.mk negValid =
      -(WeierstrassCurve.Affine.Point.mk valid) := by
  change WeierstrassCurve.Affine.Point.some x (-y) _ =
    WeierstrassCurve.Affine.Point.some x (curve.negY x y) _
  simp [WeierstrassCurve.Affine.Point.some.injEq,
    WeierstrassCurve.Affine.negY, curve]

theorem rational_neg (point : EdwardsWeierstrassEquiv01.RationalWeierstrass parameters) :
    rationalEquivalence (EdwardsWeierstrassEquiv01.weierstrassNeg parameters point) =
      -rationalEquivalence point := by
  cases point with
  | none => simp [EdwardsWeierstrassEquiv01.weierstrassNeg, rational_none]
  | some point =>
    change rationalEquivalence (some _) = -rationalEquivalence (some point)
    rw [rational_some, rational_some]
    exact mk_neg _ _

theorem equivalence_neg (point : EdwardsWeierstrassEquiv01.Edwards parameters) :
    equivalence (EdwardsWeierstrassEquiv01.edwardsNeg parameters point) = -equivalence point := by
  change rationalEquivalence (EdwardsWeierstrassEquiv01.forward parameters
      (EdwardsWeierstrassEquiv01.edwardsNeg parameters point)) =
    -rationalEquivalence (EdwardsWeierstrassEquiv01.forward parameters point)
  rw [EdwardsWeierstrassEquiv01.forward_neg]
  exact rational_neg _

theorem addition_identity_image [DecidableEq F]
    (point : EdwardsWeierstrassEquiv01.Edwards parameters) :
    equivalence (EdwardsAdditionPilot01.addition parameters point
      (EdwardsWeierstrassEquiv01.identity parameters)) =
      equivalence point + equivalence (EdwardsWeierstrassEquiv01.identity parameters) := by
  rw [EdwardsAdditionPilot01.addition_identity, equivalence_identity, add_zero]

theorem identity_addition_image [DecidableEq F]
    (point : EdwardsWeierstrassEquiv01.Edwards parameters) :
    equivalence (EdwardsAdditionPilot01.addition parameters
      (EdwardsWeierstrassEquiv01.identity parameters) point) =
      equivalence (EdwardsWeierstrassEquiv01.identity parameters) + equivalence point := by
  rw [EdwardsAdditionPilot01.identity_addition, equivalence_identity, zero_add]

theorem inverse_addition_image [DecidableEq F]
    (point : EdwardsWeierstrassEquiv01.Edwards parameters) :
    equivalence (EdwardsAdditionPilot01.addition parameters point
      (EdwardsWeierstrassEquiv01.edwardsNeg parameters point)) =
      equivalence point + equivalence (EdwardsWeierstrassEquiv01.edwardsNeg parameters point) := by
  rw [EdwardsAdditionPilot01.addition_inverse, equivalence_identity, equivalence_neg, add_neg_cancel]


set_option pp.all true in
#check @rationalEquivalence
#print axioms rationalEquivalence

set_option pp.all true in
#check @rational_none
#print axioms rational_none

set_option pp.all true in
#check @rational_some
#print axioms rational_some

set_option pp.all true in
#check @mk_neg
#print axioms mk_neg

set_option pp.all true in
#check @rational_neg
#print axioms rational_neg

set_option pp.all true in
#check @equivalence_neg
#print axioms equivalence_neg

set_option pp.all true in
#check @addition_identity_image
#print axioms addition_identity_image

set_option pp.all true in
#check @identity_addition_image
#print axioms identity_addition_image

set_option pp.all true in
#check @inverse_addition_image
#print axioms inverse_addition_image
end ShielddSecurity.ConcretePointAdditionPilot01
