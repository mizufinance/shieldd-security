import ShielddSecurity.ConcreteCardinalityJoin01
import ShielddSecurity.ConcretePointOrder01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteClosedCardinality01
open ConcretePointTorsion01 CurveCardinalityWindow01

/-- The previously traced base is a point of this same concrete Mathlib curve:
the field modulus and all five curve coefficients are definitionally equal. -/
noncomputable def base : curve.Point := by
  classical
  exact ConcretePointOperationPilot01.base

theorem base_order : addOrderOf base = scalarModulus := by
  classical
  exact ConcretePointOrder01.base_order

theorem curve_cardinality : Nat.card curve.Point = 8 * scalarModulus :=
  ConcreteCardinalityJoin01.cardinality_from_base_order base base_order

theorem global_exponent (point : curve.Point) : (8 * scalarModulus) • point = 0 :=
  ConcreteCardinalityJoin01.global_exponent_from_base_order base base_order point

end ShielddSecurity.ConcreteClosedCardinality01

set_option pp.all true in
#check @ShielddSecurity.ConcreteClosedCardinality01.base
#print axioms ShielddSecurity.ConcreteClosedCardinality01.base
set_option pp.all true in
#check @ShielddSecurity.ConcreteClosedCardinality01.base_order
#print axioms ShielddSecurity.ConcreteClosedCardinality01.base_order
set_option pp.all true in
#check @ShielddSecurity.ConcreteClosedCardinality01.curve_cardinality
#print axioms ShielddSecurity.ConcreteClosedCardinality01.curve_cardinality
set_option pp.all true in
#check @ShielddSecurity.ConcreteClosedCardinality01.global_exponent
#print axioms ShielddSecurity.ConcreteClosedCardinality01.global_exponent
