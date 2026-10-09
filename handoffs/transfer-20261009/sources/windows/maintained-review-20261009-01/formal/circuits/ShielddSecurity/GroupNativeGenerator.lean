import ShielddSecurity.GroupNativeNonidentity
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 150000

namespace ShielddSecurity.GroupNativeGenerator

/-- The exact order is a global standard-generator interpretation contract.
The scalar bounds come from canonical nonzero input construction. Neither a
desired output point nor its nonidentity is a premise. -/
theorem canonical_multiple_nonzero {J : Type} [AddCommGroup J] (generator : J)
    (exactOrder : addOrderOf generator = Scalar.order) (scalar : Nat)
    (positive : 0 < scalar) (bounded : scalar < Scalar.order) :
    scalar • generator ≠ 0 := by
  intro zero
  have divides : addOrderOf generator ∣ scalar :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr zero
  rw [exactOrder] at divides
  exact Nat.not_dvd_of_pos_of_lt positive bounded divides

theorem canonical_multiple_subgroup {J : Type} [AddCommGroup J] (generator : J)
    (exactOrder : addOrderOf generator = Scalar.order) (scalar : Nat) :
    Scalar.order • (scalar • generator) = 0 := by
  have annihilated : Scalar.order • generator = 0 := by
    rw [← exactOrder]
    exact addOrderOf_nsmul_eq_zero generator
  rw [← mul_nsmul, Nat.mul_comm, mul_nsmul, annihilated, nsmul_zero]

/-- This supplies the arithmetic legality of encryption's owned x inverse
from scalar and exact-generator contracts. Actual bit/multiply/source/row joins
are required separately to identify the EPK coordinate with this multiple. -/
theorem canonical_multiple_inverse {F J : Type} [Field F] [AddCommGroup J]
    (d : F) (model : Group.StandardCurveModel J d) (generator : J)
    (exactOrder : addOrderOf generator = Scalar.order) (scalar : Nat)
    (positive : 0 < scalar) (bounded : scalar < Scalar.order) :
    (model.coordinates (scalar • generator)).x *
      ((model.coordinates (scalar • generator)).x)⁻¹ = 1 := by
  exact GroupNativeNonidentity.nonidentity_inverse_coordinates d model (scalar • generator)
    (canonical_multiple_subgroup generator exactOrder scalar)
    (canonical_multiple_nonzero generator exactOrder scalar positive bounded)

set_option pp.all true in
#check @canonical_multiple_nonzero
#print axioms canonical_multiple_nonzero
set_option pp.all true in
#check @canonical_multiple_subgroup
#print axioms canonical_multiple_subgroup
set_option pp.all true in
#check @canonical_multiple_inverse
#print axioms canonical_multiple_inverse

end ShielddSecurity.GroupNativeGenerator
