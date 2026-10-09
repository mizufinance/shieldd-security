import ShielddSecurity.ConcretePointAdditionPilot01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointCoordinates01
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01

/-- Coordinate representation only; the remaining StandardCurveModel addition field is unproved. -/
noncomputable def coordinates (point : curve.Point) : Group.Point F :=
  (equivalence.symm point).val

theorem onCurve (point : curve.Point) : Group.OnCurve coefficient (coordinates point) :=
  (equivalence.symm point).property

theorem covers (point : Group.Point F) (valid : Group.OnCurve coefficient point) :
    ∃ represented : curve.Point, coordinates represented = point := by
  refine ⟨equivalence ⟨point, valid⟩, ?_⟩
  change (equivalence.symm (equivalence ⟨point, valid⟩)).val = point
  rw [equivalence.symm_apply_apply]

theorem injective : Function.Injective coordinates := by
  intro left right same
  apply equivalence.symm.injective
  exact Subtype.ext same

theorem identity : coordinates 0 = Group.identityPoint := by
  have inverse : equivalence.symm 0 = EdwardsWeierstrassEquiv01.identity parameters := by
    apply equivalence.injective
    rw [equivalence.apply_symm_apply, equivalence_identity]
  change (equivalence.symm 0).val = Group.identityPoint
  rw [inverse]
  rfl

theorem negation (point : curve.Point) :
    coordinates (-point) = ⟨-(coordinates point).x, (coordinates point).y⟩ := by
  have inverse : equivalence.symm (-point) =
      EdwardsWeierstrassEquiv01.edwardsNeg parameters (equivalence.symm point) := by
    apply equivalence.injective
    rw [equivalence.apply_symm_apply, ConcretePointAdditionPilot01.equivalence_neg,
      equivalence.apply_symm_apply]
  change (equivalence.symm (-point)).val = _
  rw [inverse]
  rfl

end ShielddSecurity.ConcretePointCoordinates01
