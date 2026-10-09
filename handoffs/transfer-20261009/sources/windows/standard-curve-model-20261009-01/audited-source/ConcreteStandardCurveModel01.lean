import ShielddSecurity.ConcreteTangentAddition01
import ShielddSecurity.ConcretePointCoordinates01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteStandardCurveModel01
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
open EdwardsWeierstrassEquiv01
variable [DecidableEq F]

theorem zero_x_classification (point : Edwards parameters) (zero : point.val.x = 0) :
    point = identity parameters ∨ point = torsion parameters := by
  rcases EdwardsWeierstrassAlgebra01.edwards_zero_x coefficient point.val point.property zero with one | minus
  · exact Or.inl (Subtype.ext (point_ext zero one))
  · exact Or.inr (Subtype.ext (point_ext zero minus))

/-- Addition compatibility for all Edwards points, with no assumed morphism,
group order, cardinality, or native representation premise. -/
theorem addition_image (left right : Edwards parameters) :
    ConcreteWeierstrassPoint01.equivalence (EdwardsAdditionPilot01.addition parameters left right) =
      ConcreteWeierstrassPoint01.equivalence left + ConcreteWeierstrassPoint01.equivalence right := by
  by_cases crossZero : Group.cross left.val right.val = 0
  · exact ConcretePoleAddition01.cross_zero_addition_image left right crossZero
  · by_cases leftZero : left.val.x = 0
    · rcases zero_x_classification left leftZero with one | minus
      · rw [one]
        exact ConcretePointAdditionPilot01.identity_addition_image right
      · rw [minus]
        exact ConcreteTorsionAddition01.torsion_addition_image right
    · by_cases rightZero : right.val.x = 0
      · rcases zero_x_classification right rightZero with one | minus
        · rw [one]
          exact ConcretePointAdditionPilot01.addition_identity_image left
        · rw [minus]
          exact ConcreteTorsionAddition01.addition_torsion_image left
      · by_cases sameY : left.val.y = right.val.y
        · rcases EdwardsTorsionAlgebra01.same_y_x_or_neg parameters right left sameY.symm with sameX | negX
          · have equal : right = left := Subtype.ext (point_ext sameX sameY.symm)
            subst right
            exact ConcreteTangentAddition01.regular_tangent_image left leftZero crossZero
          · have equal : right = edwardsNeg parameters left := Subtype.ext (point_ext negX sameY.symm)
            rw [equal]
            exact ConcretePointAdditionPilot01.inverse_addition_image left
        · exact ConcreteSecantAddition01.regular_secant_image left right leftZero rightZero sameY crossZero

theorem coordinate_addition (left right : curve.Point) :
    ConcretePointCoordinates01.coordinates (left + right) =
      Group.affineAdd coefficient (ConcretePointCoordinates01.coordinates left)
        (ConcretePointCoordinates01.coordinates right) := by
  have inverse : ConcreteWeierstrassPoint01.equivalence.symm (left + right) =
      EdwardsAdditionPilot01.addition parameters
        (ConcreteWeierstrassPoint01.equivalence.symm left)
        (ConcreteWeierstrassPoint01.equivalence.symm right) := by
    apply ConcreteWeierstrassPoint01.equivalence.injective
    rw [ConcreteWeierstrassPoint01.equivalence.apply_symm_apply, addition_image,
      ConcreteWeierstrassPoint01.equivalence.apply_symm_apply,
      ConcreteWeierstrassPoint01.equivalence.apply_symm_apply]
  change (ConcreteWeierstrassPoint01.equivalence.symm (left + right)).val = _
  rw [inverse]
  rfl

/-- The standard group is the actual elliptic Mathlib Point group. Coordinates
cover all Edwards curve solutions, and their addition law is proved above. -/
noncomputable def model : Group.StandardCurveModel curve.Point coefficient where
  coordinates := ConcretePointCoordinates01.coordinates
  onCurve := ConcretePointCoordinates01.onCurve
  covers := ConcretePointCoordinates01.covers
  injective := ConcretePointCoordinates01.injective
  identity := ConcretePointCoordinates01.identity
  addition := coordinate_addition


set_option pp.all true in
#check @zero_x_classification
#print axioms zero_x_classification

set_option pp.all true in
#check @addition_image
#print axioms addition_image

set_option pp.all true in
#check @coordinate_addition
#print axioms coordinate_addition

set_option pp.all true in
#check @model
#print axioms model
end ShielddSecurity.ConcreteStandardCurveModel01
