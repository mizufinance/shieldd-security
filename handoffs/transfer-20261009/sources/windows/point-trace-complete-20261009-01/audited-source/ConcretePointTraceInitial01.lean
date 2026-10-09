import ShielddSecurity.ConcretePointOperationPilot01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceInitial01
open ConcreteJubjubField01 ConcreteWeierstrassPoint01
variable [DecidableEq F]

/-- Candidate step 0's doubling of the initial infinity point. -/
theorem initial_double : (0 : curve.Point) + 0 = 0 := by
  exact zero_add 0

/-- Candidate step 0's addition of the base point to infinity. -/
theorem initial_add : (0 : curve.Point) + ConcretePointOperationPilot01.base =
    ConcretePointOperationPilot01.base := by
  exact zero_add _

/-- The first binary prefix is the actual base point. -/
theorem initial_prefix : (1 : Nat) • ConcretePointOperationPilot01.base =
    ConcretePointOperationPilot01.base := by
  exact one_nsmul _


set_option pp.all true in
#check @initial_double
#print axioms initial_double

set_option pp.all true in
#check @initial_add
#print axioms initial_add

set_option pp.all true in
#check @initial_prefix
#print axioms initial_prefix
end ShielddSecurity.ConcretePointTraceInitial01
