import ShielddSecurity.ModularPower
import ShielddSecurity.NatModularPower01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.NatModularPowerFieldSound01

theorem power_agreement (modulus base exponent : Nat) :
    NatModularPower01.power modulus base exponent =
      ModularPower.power modulus base exponent := by
  induction exponent using Nat.strong_induction_on with
  | h exponent previous =>
    rw [NatModularPower01.power, ModularPower.power]
    by_cases zero : exponent = 0
    · rw [dif_pos zero, dif_pos zero]
    · rw [dif_neg zero, dif_neg zero,
        previous (exponent / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide : 1 < 2))]

theorem power_sound (modulus base exponent : Nat) :
    (NatModularPower01.power modulus base exponent : ZMod modulus) =
      (base : ZMod modulus) ^ exponent := by
  rw [power_agreement, ModularPower.power_sound]

end ShielddSecurity.NatModularPowerFieldSound01

set_option pp.all true in
#check @ShielddSecurity.NatModularPowerFieldSound01.power_agreement
#print axioms ShielddSecurity.NatModularPowerFieldSound01.power_agreement
set_option pp.all true in
#check @ShielddSecurity.NatModularPowerFieldSound01.power_sound
#print axioms ShielddSecurity.NatModularPowerFieldSound01.power_sound
