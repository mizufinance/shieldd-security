import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ModularPower

/-- Binary exponentiation reduces each multiplication; it never constructs
the unreduced integer power. This definition does not assume primality. -/
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

theorem power_sound (modulus base exponent : Nat) :
    (power modulus base exponent : ZMod modulus) = (base : ZMod modulus) ^ exponent := by
  induction exponent using Nat.strong_induction_on with
  | h exponent previous =>
    by_cases zero : exponent = 0
    · subst exponent
      rw [power, dif_pos rfl, ZMod.natCast_mod]
      simp
    · have smaller := Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide : 1 < 2)
      rw [power, dif_neg zero]
      by_cases even : exponent % 2 = 0
      · rw [if_pos even, ZMod.natCast_mod, Nat.cast_mul, previous _ smaller]
        have count : exponent / 2 * 2 = exponent := by omega
        rw [← pow_two, ← pow_mul, count]
      · rw [if_neg even, ZMod.natCast_mod, Nat.cast_mul,
          ZMod.natCast_mod, Nat.cast_mul, previous _ smaller]
        have odd : exponent % 2 = 1 := by omega
        have count : exponent / 2 * 2 + 1 = exponent := by omega
        rw [← pow_two, ← pow_mul, ← pow_succ, count]

theorem power_eq_one (modulus base exponent : Nat)
    (checked : power modulus base exponent = 1) :
    (base : ZMod modulus) ^ exponent = 1 := by
  rw [← power_sound, checked]
  simp

theorem power_ne_one (modulus base exponent : Nat) (large : 1 < modulus)
    (checked : power modulus base exponent ≠ 1) :
    (base : ZMod modulus) ^ exponent ≠ 1 := by
  intro equal
  have casts : (power modulus base exponent : ZMod modulus) = (1 : Nat) := by
    simpa only [Nat.cast_one] using (power_sound modulus base exponent).trans equal
  have residues := (ZMod.natCast_eq_natCast_iff' _ _ modulus).mp casts
  rw [Nat.mod_eq_of_lt (power_lt modulus base exponent (by omega)),
    Nat.mod_eq_of_lt large] at residues
  exact checked residues

end ShielddSecurity.ModularPower
