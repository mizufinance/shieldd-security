import ShielddSecurity.GroupWindows

set_option maxHeartbeats 300000

namespace ShielddSecurity.TransferSubgroup

open ShielddSecurity.Group

variable {F : Type} [Field F]

/-- The existing shared inverse constraint supplies the division preconditions.
Actual row certificates must establish these three polynomial equations; no
claim about the witness-generation closure is used. -/
theorem shared_inverse_affine (d inverse : F) (left right output : Point F)
    (inverseRow : ((1 + delta d left right) * (1 - delta d left right)) * inverse = 1)
    (xValue : output.x = cross left right * (1 - delta d left right) * inverse)
    (yValue : output.y = diagonal left right * (1 + delta d left right) * inverse) :
    output = affineAdd d left right := by
  have plus : 1 + delta d left right ≠ 0 := by
    intro zero
    rw [zero, zero_mul, zero_mul] at inverseRow
    exact zero_ne_one inverseRow
  have minus : 1 - delta d left right ≠ 0 := by
    intro zero
    rw [zero, mul_zero, zero_mul] at inverseRow
    exact zero_ne_one inverseRow
  have equations := shared_inverse_rows d inverse left right output inverseRow xValue yValue
  have hx := quotient_sound _ _ _ plus equations.1
  have hy := quotient_sound _ _ _ minus equations.2
  cases output
  simp_all only [affineAdd, Point.mk.injEq]

/-- Three constrained affine doubles, coordinate binding and the independent
x-inverse yield a nonidentity point in the r-annihilated standard subgroup.
The standard curve model and its global order are explicit imported contracts.
The named row equations and source-role bindings remain Shieldd obligations. -/
theorem cofactor_nonidentity {J : Type} [AddCommGroup J]
    (d : F) (model : StandardCurveModel J d) (r : Nat)
    (standardOrder : ∀ point : J, (8 * r) • point = 0)
    (preimage twice four eight boundPoint : Point F) (valid : OnCurve d preimage)
    (first : twice = affineAdd d preimage preimage)
    (second : four = affineAdd d twice twice)
    (third : eight = affineAdd d four four)
    (binding : boundPoint = eight) (inverse : F) (nonidentity : inverse * boundPoint.x = 1) :
    ∃ represented : J, model.coordinates represented = boundPoint ∧
      r • represented = 0 ∧ represented ≠ 0 := by
  obtain ⟨represented, coordinates, order⟩ := cofactor_image_annihilated
    d model r standardOrder preimage twice four eight valid first second third
  have coordinatesPublic : model.coordinates represented = boundPoint := coordinates.trans binding.symm
  have nonzero : boundPoint.x ≠ 0 := by
    intro zero
    rw [zero, mul_zero] at nonidentity
    exact zero_ne_one nonidentity
  refine ⟨represented, coordinatesPublic, order, ?_⟩
  apply represented_nonidentity d model represented
  rw [coordinatesPublic]
  exact nonzero

set_option pp.all true in
#check @shared_inverse_affine
#print axioms shared_inverse_affine
set_option pp.all true in
#check @cofactor_nonidentity
#print axioms cofactor_nonidentity

end ShielddSecurity.TransferSubgroup
