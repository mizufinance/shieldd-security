import ShielddSecurity.ConcreteTorsionAddition01
import ShielddSecurity.EdwardsExceptionalClassification01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePoleAddition01
open EdwardsWeierstrassEquiv01

section Generic
variable {F : Type} [Field F] (params : Parameters F)

def oppositeY (point : Edwards params) : Edwards params :=
  ⟨⟨point.val.x, -point.val.y⟩, by simpa [Group.OnCurve] using point.property⟩

theorem oppositeY_translate (point : Edwards params) :
    oppositeY params point =
      EdwardsAdditionPilot01.torsionTranslate params (edwardsNeg params point) := by
  apply Subtype.ext
  apply point_ext <;> simp [oppositeY, EdwardsAdditionPilot01.torsionTranslate, edwardsNeg]

theorem addition_oppositeY (point : Edwards params) :
    EdwardsAdditionPilot01.addition params point (oppositeY params point) = torsion params := by
  have den := Group.denominators_nonzero params.d params.imaginary params.nonSquare
    params.imaginarySquare point.val (oppositeY params point).val point.property
      (oppositeY params point).property
  apply Subtype.ext
  apply point_ext
  · change (point.val.x * -point.val.y + point.val.y * point.val.x) / _ = 0
    rw [show point.val.x * -point.val.y + point.val.y * point.val.x = 0 by ring]
    exact zero_div _
  · change (point.val.y * -point.val.y + point.val.x * point.val.x) /
        (1 - params.d * point.val.x * point.val.x * point.val.y * -point.val.y) = -1
    apply (div_eq_iff den.2).mpr
    have curve := point.property
    unfold Group.OnCurve at curve
    dsimp only [Group.delta, oppositeY]
    linear_combination -curve

/-- The poles of the addition map are classified from the curve equations,
without assuming associativity or a cancellation law for Edwards addition. -/
theorem cross_zero_pair (left right : Edwards params)
    (zero : Group.cross left.val right.val = 0) :
    right = edwardsNeg params left ∨ right = oppositeY params left := by
  by_cases zeroY : left.val.y = 0
  · have squares := EdwardsExceptionalClassification01.cross_zero_y_square params left right zero
    have rightZero : right.val.y = 0 := by
      apply mul_self_eq_zero.mp
      simpa only [zeroY, zero_mul] using squares.symm
    have same : right.val.y = left.val.y := by rw [rightZero, zeroY]
    rcases EdwardsTorsionAlgebra01.same_y_x_or_neg params right left same with sameX | negX
    · right
      apply Subtype.ext
      apply point_ext
      · exact sameX
      · change right.val.y = -left.val.y
        rw [rightZero, zeroY, neg_zero]
    · left
      apply Subtype.ext
      exact point_ext negX same
  · rcases EdwardsExceptionalClassification01.cross_zero_y_or_neg params left right zero with same | opposite
    · have product : (left.val.x + right.val.x) * left.val.y = 0 := by
        unfold Group.cross at zero
        rw [← same] at zero
        linear_combination zero
      have negX : right.val.x = -left.val.x :=
        eq_neg_of_add_eq_zero_right ((mul_eq_zero.mp product).resolve_right zeroY)
      left
      apply Subtype.ext
      exact point_ext negX same.symm
    · have product : (right.val.x - left.val.x) * left.val.y = 0 := by
        unfold Group.cross at zero
        have rightY : right.val.y = -left.val.y := by linear_combination opposite
        rw [rightY] at zero
        linear_combination zero
      have sameX : right.val.x = left.val.x :=
        sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_right zeroY)
      right
      apply Subtype.ext
      apply point_ext
      · exact sameX
      · change right.val.y = -left.val.y
        linear_combination opposite
end Generic

open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]

theorem oppositeY_image (point : Edwards parameters) :
    ConcreteWeierstrassPoint01.equivalence (oppositeY parameters point) =
      ConcreteWeierstrassPoint01.equivalence (torsion parameters) -
        ConcreteWeierstrassPoint01.equivalence point := by
  rw [oppositeY_translate, ← EdwardsAdditionPilot01.torsion_addition,
    ConcreteTorsionAddition01.torsion_addition_image]
  rw [ConcretePointAdditionPilot01.equivalence_neg, sub_eq_add_neg]

theorem oppositeY_addition_image (point : Edwards parameters) :
    ConcreteWeierstrassPoint01.equivalence (EdwardsAdditionPilot01.addition parameters
      point (oppositeY parameters point)) =
      ConcreteWeierstrassPoint01.equivalence point +
        ConcreteWeierstrassPoint01.equivalence (oppositeY parameters point) := by
  rw [addition_oppositeY, oppositeY_image]
  abel

theorem cross_zero_addition_image (left right : Edwards parameters)
    (zero : Group.cross left.val right.val = 0) :
    ConcreteWeierstrassPoint01.equivalence (EdwardsAdditionPilot01.addition parameters left right) =
      ConcreteWeierstrassPoint01.equivalence left + ConcreteWeierstrassPoint01.equivalence right := by
  rcases cross_zero_pair parameters left right zero with inverse | opposite
  · rw [inverse]
    exact ConcretePointAdditionPilot01.inverse_addition_image left
  · rw [opposite]
    exact oppositeY_addition_image left


set_option pp.all true in
#check @oppositeY
#print axioms oppositeY

set_option pp.all true in
#check @oppositeY_translate
#print axioms oppositeY_translate

set_option pp.all true in
#check @addition_oppositeY
#print axioms addition_oppositeY

set_option pp.all true in
#check @cross_zero_pair
#print axioms cross_zero_pair

set_option pp.all true in
#check @oppositeY_image
#print axioms oppositeY_image

set_option pp.all true in
#check @oppositeY_addition_image
#print axioms oppositeY_addition_image

set_option pp.all true in
#check @cross_zero_addition_image
#print axioms cross_zero_addition_image
end ShielddSecurity.ConcretePoleAddition01
