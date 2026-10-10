import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.NatModularPower01

/-- Exact integer binary exponentiation recurrence from ModularPower.
The field interpretation is a separate obligation. -/
def power (modulus base exponent : Nat) : Nat :=
  if zero : exponent = 0 then 1 % modulus
  else
    let half := power modulus base (exponent / 2)
    let square := (half * half) % modulus
    if exponent % 2 = 0 then square else (square * base) % modulus
termination_by exponent
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)

theorem power_lt (modulus base exponent : Nat) (positive : 0 < modulus) :
    power modulus base exponent < modulus := by
  rw [power]
  split
  · exact Nat.mod_lt _ positive
  · split <;> exact Nat.mod_lt _ positive

end ShielddSecurity.NatModularPower01

set_option pp.all true in
#check @ShielddSecurity.NatModularPower01.power
#print axioms ShielddSecurity.NatModularPower01.power
set_option pp.all true in
#check @ShielddSecurity.NatModularPower01.power_lt
#print axioms ShielddSecurity.NatModularPower01.power_lt
