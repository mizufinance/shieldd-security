import ShielddSecurity.TorsionEulerResidue01
import ShielddSecurity.EulerNonsquare01
import Mathlib.Data.Fintype.Units
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TorsionPrimeNonsquare01
open TorsionEulerInteger49

/-- This module retains the explicit primality premise until the independently
checked Lucas certificate is connected. It proves no curve cardinality claim. -/
variable [Fact (Nat.Prime modulus)]

theorem fermat (value : ZMod modulus) (nonzero : value ≠ 0) :
    value ^ (2 * half) = 1 := by
  classical
  have twice : 2 * half = modulus - 1 := by
    rw [Nat.mul_comm, half_twice]
  rw [twice, ← ZMod.card modulus]
  calc
    _ = (Units.mk0 value nonzero ^ (Fintype.card (ZMod modulus) - 1) : (ZMod modulus)ˣ).1 := by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    _ = 1 := by rw [← Fintype.card_units, pow_card_eq_one]; rfl

theorem minus_one : ((modulus - 1 : Nat) : ZMod modulus) = -1 := by
  have count : modulus - 1 + 1 = modulus := by decide +kernel
  have cast := congrArg (fun value : Nat => (value : ZMod modulus)) count
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at cast
  exact eq_neg_of_add_eq_zero_left cast

theorem two_ne_zero : (2 : ZMod modulus) ≠ 0 := by
  intro zero
  have divides : modulus ∣ 2 :=
    (CharP.cast_eq_zero_iff (ZMod modulus) modulus 2).mp
      (by simpa only [Nat.cast_ofNat] using zero)
  exact Nat.not_le_of_gt (by decide +kernel : 2 < modulus)
    (Nat.le_of_dvd (by decide : 0 < 2) divides)

theorem nonsquare_of_residue (value : ZMod modulus)
    (residue : value ^ half = ((modulus - 1 : Nat) : ZMod modulus)) :
    WeierstrassTwoTorsionAlgebra01.NoSquare value := by
  have euler : value ^ half = -1 := residue.trans minus_one
  have nonzero : value ≠ 0 := by
    intro zero
    rw [zero, zero_pow (by decide +kernel : half ≠ 0)] at euler
    exact neg_ne_zero.mpr (one_ne_zero : (1 : ZMod modulus) ≠ 0) euler.symm
  exact EulerNonsquare01.nonsquare_from_euler value half nonzero two_ne_zero fermat euler

theorem first_nonsquare : WeierstrassTwoTorsionAlgebra01.NoSquare
    (firstX : ZMod modulus) := nonsquare_of_residue _ TorsionEulerResidue01.first_residue

theorem second_nonsquare : WeierstrassTwoTorsionAlgebra01.NoSquare
    (secondX : ZMod modulus) := nonsquare_of_residue _ TorsionEulerResidue01.second_residue

theorem discriminant_nonsquare : WeierstrassTwoTorsionAlgebra01.NoSquare
    (quadraticDiscriminant : ZMod modulus) :=
  nonsquare_of_residue _ TorsionEulerResidue01.discriminant_residue

end ShielddSecurity.TorsionPrimeNonsquare01

set_option pp.all true in
#check @ShielddSecurity.TorsionPrimeNonsquare01.fermat
#print axioms ShielddSecurity.TorsionPrimeNonsquare01.fermat
set_option pp.all true in
#check @ShielddSecurity.TorsionPrimeNonsquare01.minus_one
#print axioms ShielddSecurity.TorsionPrimeNonsquare01.minus_one
set_option pp.all true in
#check @ShielddSecurity.TorsionPrimeNonsquare01.two_ne_zero
#print axioms ShielddSecurity.TorsionPrimeNonsquare01.two_ne_zero
set_option pp.all true in
#check @ShielddSecurity.TorsionPrimeNonsquare01.nonsquare_of_residue
#print axioms ShielddSecurity.TorsionPrimeNonsquare01.nonsquare_of_residue
set_option pp.all true in
#check @ShielddSecurity.TorsionPrimeNonsquare01.first_nonsquare
#print axioms ShielddSecurity.TorsionPrimeNonsquare01.first_nonsquare
set_option pp.all true in
#check @ShielddSecurity.TorsionPrimeNonsquare01.second_nonsquare
#print axioms ShielddSecurity.TorsionPrimeNonsquare01.second_nonsquare
set_option pp.all true in
#check @ShielddSecurity.TorsionPrimeNonsquare01.discriminant_nonsquare
#print axioms ShielddSecurity.TorsionPrimeNonsquare01.discriminant_nonsquare
