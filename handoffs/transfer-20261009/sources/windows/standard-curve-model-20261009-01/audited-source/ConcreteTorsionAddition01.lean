import ShielddSecurity.ConcreteOriginAdditionPilot01
import ShielddSecurity.ConcretePointAdditionPilot01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteTorsionAddition01
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
open EdwardsWeierstrassAlgebra01 EdwardsWeierstrassEquiv01
variable [DecidableEq F]

theorem regular_minus (point : Edwards parameters) (nonzeroX : point.val.x ≠ 0) :
    point.val.y ≠ 1 := by
  intro equal
  exact nonzeroX (EdwardsWeierstrassAlgebra01.edwards_one_y coefficient point.val
    point.property (oneAdd parameters) equal)

theorem regular_plus (point : Edwards parameters) (nonzeroX : point.val.x ≠ 0) :
    point.val.y ≠ -1 := by
  intro equal
  exact nonzeroX (EdwardsWeierstrassAlgebra01.edwards_neg_one_y coefficient point.val
    point.property (oneAdd parameters) equal)

theorem regular_equivalence (point : Edwards parameters) (nonzeroX : point.val.x ≠ 0)
    (valid : curve.Equation (forwardX B point.val.x point.val.y)
      (forwardY B point.val.x point.val.y)) :
    ConcreteWeierstrassPoint01.equivalence point = WeierstrassCurve.Affine.Point.mk valid := by
  have notOne := regular_minus point nonzeroX
  change ConcretePointAdditionPilot01.rationalEquivalence (forward parameters point) = _
  simp only [forward, dif_neg notOne, dif_neg nonzeroX]
  exact ConcretePointAdditionPilot01.rational_some _

theorem regular_torsion_image (point : Edwards parameters) (nonzeroX : point.val.x ≠ 0) :
    ConcreteWeierstrassPoint01.equivalence (EdwardsAdditionPilot01.torsionTranslate parameters point) =
      ConcreteWeierstrassPoint01.equivalence (torsion parameters) +
        ConcreteWeierstrassPoint01.equivalence point := by
  have notOne := regular_minus point nonzeroX
  have notNegOne := regular_plus point nonzeroX
  have minus : 1 - point.val.y ≠ 0 := fun equal => notOne (sub_eq_zero.mp equal).symm
  have plus : 1 + point.val.y ≠ 0 := fun equal => notNegOne (eq_neg_of_add_eq_zero_right equal)
  have valid := (equation_iff _ _).mp (EdwardsWeierstrassMap01.forward_on_curve
    coefficient A B point.val.x point.val.y nonzeroX minus
    (positive parameters) (negative parameters) point.property)
  have nonzeroForward : forwardX B point.val.x point.val.y ≠ 0 := by
    unfold forwardX
    exact div_ne_zero (mul_ne_zero (nonzeroB parameters) plus) minus
  obtain ⟨output, equality⟩ := ConcreteOriginAdditionPilot01.origin_add_coordinates valid nonzeroForward
  let translated := EdwardsAdditionPilot01.torsionTranslate parameters point
  have translatedNonzero : translated.val.x ≠ 0 := neg_ne_zero.mpr nonzeroX
  have translatedNotOne := regular_minus translated translatedNonzero
  have translatedMinus : 1 - translated.val.y ≠ 0 :=
    fun equal => translatedNotOne (sub_eq_zero.mp equal).symm
  have translatedValid := (equation_iff _ _).mp (EdwardsWeierstrassMap01.forward_on_curve
    coefficient A B translated.val.x translated.val.y translatedNonzero translatedMinus
    (positive parameters) (negative parameters) translated.property)
  have xValue : forwardX B translated.val.x translated.val.y = B * B / forwardX B point.val.x point.val.y := by
    apply (eq_div_iff nonzeroForward).mpr
    exact EdwardsTorsionAlgebra01.forward_torsion_x B point.val.x point.val.y minus plus
  have yValue : forwardY B translated.val.x translated.val.y =
      -B * B * forwardY B point.val.x point.val.y / forwardX B point.val.x point.val.y ^ 2 := by
    apply (eq_div_iff (pow_ne_zero _ nonzeroForward)).mpr
    exact EdwardsTorsionAlgebra01.forward_torsion_y B point.val.x point.val.y nonzeroX minus plus
  rw [equivalence_torsion, regular_equivalence point nonzeroX valid,
    regular_equivalence translated translatedNonzero translatedValid, equality]
  change WeierstrassCurve.Affine.Point.some _ _ _ = WeierstrassCurve.Affine.Point.some _ _ _
  simp only [WeierstrassCurve.Affine.Point.some.injEq, xValue, yValue, and_self]

theorem torsion_addition_image (point : Edwards parameters) :
    ConcreteWeierstrassPoint01.equivalence (EdwardsAdditionPilot01.addition parameters
      (torsion parameters) point) =
      ConcreteWeierstrassPoint01.equivalence (torsion parameters) +
        ConcreteWeierstrassPoint01.equivalence point := by
  by_cases nonzeroX : point.val.x = 0
  · rcases EdwardsWeierstrassAlgebra01.edwards_zero_x coefficient point.val point.property nonzeroX with one | minusOne
    · have equal : point = identity parameters :=
        Subtype.ext (point_ext nonzeroX one)
      rw [equal, EdwardsAdditionPilot01.addition_identity, equivalence_identity, add_zero]
    · have equal : point = torsion parameters :=
        Subtype.ext (point_ext nonzeroX minusOne)
      rw [equal, EdwardsAdditionPilot01.torsion_addition]
      have translated : EdwardsAdditionPilot01.torsionTranslate parameters (torsion parameters) =
          identity parameters := by
        apply Subtype.ext
        simp [EdwardsAdditionPilot01.torsionTranslate, torsion, identity]
      rw [translated, equivalence_identity, equivalence_torsion,
        ConcreteOriginAdditionPilot01.origin_add_origin]
  · rw [EdwardsAdditionPilot01.torsion_addition]
    exact regular_torsion_image point nonzeroX

theorem addition_torsion_image (point : Edwards parameters) :
    ConcreteWeierstrassPoint01.equivalence (EdwardsAdditionPilot01.addition parameters
      point (torsion parameters)) =
      ConcreteWeierstrassPoint01.equivalence point +
        ConcreteWeierstrassPoint01.equivalence (torsion parameters) := by
  rw [EdwardsAdditionPilot01.addition_comm, torsion_addition_image, add_comm]


set_option pp.all true in
#check @regular_minus
#print axioms regular_minus

set_option pp.all true in
#check @regular_plus
#print axioms regular_plus

set_option pp.all true in
#check @regular_equivalence
#print axioms regular_equivalence

set_option pp.all true in
#check @regular_torsion_image
#print axioms regular_torsion_image

set_option pp.all true in
#check @torsion_addition_image
#print axioms torsion_addition_image

set_option pp.all true in
#check @addition_torsion_image
#print axioms addition_torsion_image
end ShielddSecurity.ConcreteTorsionAddition01
