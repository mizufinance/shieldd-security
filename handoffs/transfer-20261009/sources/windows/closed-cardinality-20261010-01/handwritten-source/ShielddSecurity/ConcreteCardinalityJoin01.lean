import ShielddSecurity.ConcreteNoSixteen01
import ShielddSecurity.CurveCardinalityImage01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteCardinalityJoin01
open ConcretePointTorsion01 ConcreteEightTorsionWitness01 CurveCardinalityWindow01

/-- All curve-side cardinality obligations are discharged. The exact base order
must still come from the separately bound runtime-base trace proof. -/
theorem cardinality_from_base_order (base : curve.Point)
    (baseOrder : addOrderOf base = scalarModulus) :
    Nat.card curve.Point = 8 * scalarModulus := by
  apply CurveCardinalityImage01.cardinality_from_image
    (DoublingKernelBound01.multiply (J := curve.Point) 8) kernel_cardinality base baseOrder
    ConcreteNoSixteen01.odd_eight_image
  exact point_cardinality_bound

theorem global_exponent_from_base_order (base : curve.Point)
    (baseOrder : addOrderOf base = scalarModulus) (point : curve.Point) :
    (8 * scalarModulus) • point = 0 := by
  apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
  rw [← cardinality_from_base_order base baseOrder]
  exact addOrderOf_dvd_natCard point

end ShielddSecurity.ConcreteCardinalityJoin01

set_option pp.all true in
#check @ShielddSecurity.ConcreteCardinalityJoin01.cardinality_from_base_order
#print axioms ShielddSecurity.ConcreteCardinalityJoin01.cardinality_from_base_order
set_option pp.all true in
#check @ShielddSecurity.ConcreteCardinalityJoin01.global_exponent_from_base_order
#print axioms ShielddSecurity.ConcreteCardinalityJoin01.global_exponent_from_base_order
