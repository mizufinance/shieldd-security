import Mathlib.Algebra.Group.Defs

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointScalarRecurrence01

variable {G : Type*} [AddMonoid G]

/-- One binary doubling step, stated symbolically for every prefix. -/
theorem even_prefix (n : Nat) (point : G) :
    (n + n) • point = n • point + n • point := by
  exact add_nsmul point n n

/-- One binary doubling-and-addition step, stated symbolically. -/
theorem odd_prefix (n : Nat) (point : G) :
    (n + n + 1) • point = (n • point + n • point) + point := by
  rw [add_nsmul, add_nsmul, one_nsmul]


set_option pp.all true in
#check @even_prefix
#print axioms even_prefix

set_option pp.all true in
#check @odd_prefix
#print axioms odd_prefix
end ShielddSecurity.ConcretePointScalarRecurrence01
