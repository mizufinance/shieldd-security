import ShielddSecurity.NatModularPowerFieldSound01
import ShielddSecurity.TorsionEulerInteger49

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TorsionEulerResidue01
open TorsionEulerInteger49

/-- Residues in the actual ZMod modulus. No primality or field instance is
assumed or concluded by these semiring power identities. -/
theorem first_residue : (firstX : ZMod modulus) ^ half = ((modulus - 1 : Nat) : ZMod modulus) := by
  rw [← NatModularPowerFieldSound01.power_sound, first_euler_checked]

theorem second_residue : (secondX : ZMod modulus) ^ half = ((modulus - 1 : Nat) : ZMod modulus) := by
  rw [← NatModularPowerFieldSound01.power_sound, second_euler_checked]

theorem discriminant_residue :
    (quadraticDiscriminant : ZMod modulus) ^ half = ((modulus - 1 : Nat) : ZMod modulus) := by
  rw [← NatModularPowerFieldSound01.power_sound, discriminant_euler_checked]

end ShielddSecurity.TorsionEulerResidue01

set_option pp.all true in
#check @ShielddSecurity.TorsionEulerResidue01.first_residue
#print axioms ShielddSecurity.TorsionEulerResidue01.first_residue
set_option pp.all true in
#check @ShielddSecurity.TorsionEulerResidue01.second_residue
#print axioms ShielddSecurity.TorsionEulerResidue01.second_residue
set_option pp.all true in
#check @ShielddSecurity.TorsionEulerResidue01.discriminant_residue
#print axioms ShielddSecurity.TorsionEulerResidue01.discriminant_residue
