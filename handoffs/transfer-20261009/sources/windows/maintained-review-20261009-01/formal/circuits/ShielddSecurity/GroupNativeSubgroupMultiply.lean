import ShielddSecurity.GroupNativeGenerator

set_option maxHeartbeats 150000

namespace ShielddSecurity.GroupNativeSubgroupMultiply

/-- The prime subgroup order is a global standard-curve contract. Input
nonidentity comes from the independent native input guard; no property of the
desired multiplication output is a premise. -/
theorem input_exact_order {J : Type} [AddCommGroup J]
    (standardPrime : Nat.Prime Scalar.order) (point : J)
    (subgroup : Scalar.order • point = 0) (nonidentity : point ≠ 0) :
    addOrderOf point = Scalar.order := by
  have divides : addOrderOf point ∣ Scalar.order :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr subgroup
  rcases standardPrime.eq_one_or_self_of_dvd (addOrderOf point) divides with one | same
  · exact False.elim (nonidentity (AddMonoid.addOrderOf_eq_one_iff.mp one))
  · exact same

theorem canonical_input_multiple_nonzero {J : Type} [AddCommGroup J]
    (standardPrime : Nat.Prime Scalar.order) (point : J)
    (subgroup : Scalar.order • point = 0) (nonidentity : point ≠ 0)
    (scalar : Nat) (positive : 0 < scalar) (bounded : scalar < Scalar.order) :
    scalar • point ≠ 0 :=
  GroupNativeGenerator.canonical_multiple_nonzero point
    (input_exact_order standardPrime point subgroup nonidentity) scalar positive bounded

/-- Arithmetic legality of the actual DH x reciprocal follows from the
independent native input guard and the owned FVK scalar bounds. Exact native
multiply/LC/row correspondence is supplied by the separate constructor join. -/
theorem canonical_input_multiple_inverse {F J : Type} [Field F] [AddCommGroup J]
    (d : F) (model : Group.StandardCurveModel J d)
    (standardPrime : Nat.Prime Scalar.order) (point : J)
    (subgroup : Scalar.order • point = 0) (nonidentity : point ≠ 0)
    (scalar : Nat) (positive : 0 < scalar) (bounded : scalar < Scalar.order) :
    (model.coordinates (scalar • point)).x *
      ((model.coordinates (scalar • point)).x)⁻¹ = 1 :=
  GroupNativeGenerator.canonical_multiple_inverse d model point
    (input_exact_order standardPrime point subgroup nonidentity) scalar positive bounded

set_option pp.all true in
#check @input_exact_order
#print axioms input_exact_order
set_option pp.all true in
#check @canonical_input_multiple_nonzero
#print axioms canonical_input_multiple_nonzero
set_option pp.all true in
#check @canonical_input_multiple_inverse
#print axioms canonical_input_multiple_inverse

end ShielddSecurity.GroupNativeSubgroupMultiply
