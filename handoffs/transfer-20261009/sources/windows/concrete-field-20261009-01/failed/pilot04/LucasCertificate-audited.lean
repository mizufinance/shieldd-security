import ShielddSecurity.ModularPower
import Mathlib.NumberTheory.LucasPrimality

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.LucasCertificate

structure FactorPower where
  factor : Nat
  exponent : Nat
  residue : Nat

structure Certificate where
  n : Nat
  base : Nat
  powers : List FactorPower

def FactorPower.check (n base : Nat) (entry : FactorPower) : Bool :=
  decide (entry.exponent = (n - 1) / entry.factor) &&
    decide (ModularPower.power n base entry.exponent = entry.residue) &&
    decide (entry.residue ≠ 1)

def Certificate.check (certificate : Certificate) : Bool :=
  decide (1 < certificate.n) &&
    decide ((certificate.powers.map FactorPower.factor).prod = certificate.n - 1) &&
    decide (ModularPower.power certificate.n certificate.base (certificate.n - 1) = 1) &&
    certificate.powers.all (FactorPower.check certificate.n certificate.base)

theorem factor_power_sound (n base : Nat) (large : 1 < n) (entry : FactorPower)
    (checked : entry.check n base = true) :
    (base : ZMod n) ^ ((n - 1) / entry.factor) ≠ 1 := by
  have facts : entry.exponent = (n - 1) / entry.factor ∧
      ModularPower.power n base entry.exponent = entry.residue ∧ entry.residue ≠ 1 := by
    simpa [FactorPower.check, Bool.and_eq_true, and_assoc] using checked
  apply ModularPower.power_ne_one n base _ large
  rw [← facts.1, facts.2.1]
  exact facts.2.2

theorem prime_divisor_member (factors : List Nat)
    (primes : ∀ factor ∈ factors, Nat.Prime factor) (q : Nat) (prime : Nat.Prime q)
    (divides : q ∣ factors.prod) : q ∈ factors := by
  induction factors with
  | nil =>
    have unit : q = 1 := Nat.dvd_one.mp (by simpa using divides)
    exact (prime.ne_one unit).elim
  | cons factor tail previous =>
    rcases (prime.dvd_mul).mp (by simpa only [List.prod_cons] using divides) with head | rest
    · have equal := (Nat.prime_dvd_prime_iff_eq prime (primes factor (by simp))).mp head
      simp [equal]
    · exact List.mem_cons_of_mem _ (previous (fun x member => primes x (by simp [member])) rest)

/-- Factor primality is obtained independently from previously checked child
certificates. The checker proves factor coverage and all Lucas power tests. -/
theorem certificate_sound (certificate : Certificate)
    (primes : ∀ entry ∈ certificate.powers, Nat.Prime entry.factor)
    (checked : certificate.check = true) : Nat.Prime certificate.n := by
  have facts : 1 < certificate.n ∧
      (certificate.powers.map FactorPower.factor).prod = certificate.n - 1 ∧
      ModularPower.power certificate.n certificate.base (certificate.n - 1) = 1 ∧
      ∀ entry ∈ certificate.powers, entry.check certificate.n certificate.base = true := by
    simpa [Certificate.check, Bool.and_eq_true, List.all_eq_true, and_assoc] using checked
  apply lucas_primality certificate.n (certificate.base : ZMod certificate.n)
    (ModularPower.power_eq_one _ _ _ facts.2.2.1)
  intro q prime divides
  have factorPrimes : ∀ factor ∈ certificate.powers.map FactorPower.factor, Nat.Prime factor := by
    intro factor member
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    exact primes entry present
  have member := prime_divisor_member (certificate.powers.map FactorPower.factor) factorPrimes q prime
    (by rw [facts.2.1]; exact divides)
  obtain ⟨entry, present, equal⟩ := List.mem_map.mp member
  rw [← equal]
  exact factor_power_sound _ _ facts.1 entry (facts.2.2.2 entry present)


set_option pp.all true in
#check @factor_power_sound
#print axioms factor_power_sound

set_option pp.all true in
#check @prime_divisor_member
#print axioms prime_divisor_member

set_option pp.all true in
#check @certificate_sound
#print axioms certificate_sound
end ShielddSecurity.LucasCertificate
