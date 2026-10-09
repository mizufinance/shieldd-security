import ShielddSecurity.ConcretePointTraceComposition01
import ShielddSecurity.SubgroupOrderPrime06
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointOrder01
open ConcreteJubjubField01 ConcreteWeierstrassPoint01
variable [DecidableEq F]

/-- Exact order follows from certified primality, annihilation, and nonidentity. -/
theorem base_order : addOrderOf ConcretePointOperationPilot01.base = Scalar.order := by
  letI : Fact (Nat.Prime Scalar.order) := ⟨SubgroupOrderPrime06.order_prime⟩
  exact addOrderOf_eq_prime ConcretePointTraceComposition01.order_annihilates
    ConcretePointTraceComposition01.base_nonzero


set_option pp.all true in
#check @base_order
#print axioms base_order
end ShielddSecurity.ConcretePointOrder01
