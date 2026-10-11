import ShielddSecurity.GroupByteCodec

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupNativeNonidentity

variable {F : Type} [Field F]

/-- The x=0 native affine boundary has order dividing two. This is derived
from the curve equation and standard addition, with no assumption about y's
sign, the desired subgroup result, or an inverse witness. -/
theorem x_zero_two_torsion {J : Type} [AddCommGroup J] (d : F)
    (model : Group.StandardCurveModel J d) (point : J)
    (zero : (model.coordinates point).x = 0) : (2 : Nat) • point = 0 := by
  have square : (model.coordinates point).y * (model.coordinates point).y = 1 := by
    have equation := model.onCurve point
    simpa only [Group.OnCurve,zero,mul_zero,zero_mul,sub_zero,add_zero] using equation
  have doubled : model.coordinates (point + point) = model.coordinates 0 := by
    rw [model.addition,model.identity]
    simp only [Group.affineAdd,Group.cross,Group.diagonal,Group.delta,Group.identityPoint,
      zero,mul_zero,zero_mul,zero_add,add_zero,sub_zero,square,div_one]
  exact (two_nsmul point).trans (model.injective doubled)

/-- Pinned group.rs191-193's x inverse is legal for an independently admitted
nonidentity subgroup input. The other x=0 affine point is excluded by the odd
prime-subgroup order, rather than silently assuming that x is nonzero. -/
theorem subgroup_nonidentity_x {J : Type} [AddCommGroup J] (d : F)
    (model : Group.StandardCurveModel J d) (point : J)
    (subgroup : Scalar.order • point = 0) (nonidentity : point ≠ 0) :
    (model.coordinates point).x ≠ 0 := by
  intro zero
  have doubled := x_zero_two_torsion d model point zero
  have odd : Scalar.order = 2 * (Scalar.order / 2) + 1 := by
    norm_num [Scalar.order]
  have annihilated : Scalar.order • point = point := by
    rw [odd,add_nsmul,mul_nsmul,doubled,
      nsmul_zero,one_nsmul,zero_add]
  exact nonidentity (annihilated.symm.trans subgroup)

/-- Construct the native reciprocal used by assert_non_identity. Actual
inverse/product row ownership and coverage are separate extracted certificates;
this theorem discharges the arithmetic legality/value without a Satisfies
premise or an assumed inverse equation for the desired circuit assignment. -/
theorem nonidentity_inverse_coordinates {J : Type} [AddCommGroup J] (d : F)
    (model : Group.StandardCurveModel J d) (point : J)
    (subgroup : Scalar.order • point = 0) (nonidentity : point ≠ 0) :
    (model.coordinates point).x * ((model.coordinates point).x)⁻¹ = 1 := by
  exact mul_inv_cancel₀ (subgroup_nonidentity_x d model point subgroup nonidentity)

set_option pp.all true in
#check @x_zero_two_torsion
#print axioms x_zero_two_torsion
set_option pp.all true in
#check @subgroup_nonidentity_x
#print axioms subgroup_nonidentity_x
set_option pp.all true in
#check @nonidentity_inverse_coordinates
#print axioms nonidentity_inverse_coordinates

end ShielddSecurity.GroupNativeNonidentity
