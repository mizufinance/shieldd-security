import ShielddSecurity.ConcretePointTraceInitial01
import ShielddSecurity.ConcretePointTraceStep251

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceComposition01
open ConcreteJubjubField01 ConcreteWeierstrassPoint01
variable [DecidableEq F]

/-- The concrete affine base point is distinct from the group identity. -/
theorem base_nonzero : ConcretePointOperationPilot01.base ≠ (0 : curve.Point) := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ConcretePointOperationPilot01.base_valid)

/-- The scalar constant is annihilating for the actual Mathlib Point group law. -/
theorem order_annihilates : Scalar.order • ConcretePointOperationPilot01.base =
    (0 : curve.Point) := ConcretePointTraceStep251.scalar_zero

/-- The initial binary prefix and the endpoint use the same concrete base point. -/
theorem trace_endpoints :
    (0 : curve.Point) + 0 = 0 ∧
    (0 : curve.Point) + ConcretePointOperationPilot01.base =
      ConcretePointOperationPilot01.base ∧
    (1 : Nat) • ConcretePointOperationPilot01.base =
      ConcretePointOperationPilot01.base ∧
    Scalar.order • ConcretePointOperationPilot01.base = 0 :=
  ⟨ConcretePointTraceInitial01.initial_double,
    ConcretePointTraceInitial01.initial_add,
    ConcretePointTraceInitial01.initial_prefix, order_annihilates⟩

end ShielddSecurity.ConcretePointTraceComposition01
