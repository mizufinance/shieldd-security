import ShielddSecurity.TransferScalarInverseCorrectness01
import Mathlib.GroupTheory.OrderOfElement
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarPublicOrders01
open TransferScalarPublicConstants01
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
open LucasCertificate
/-! Exact source public Montgomery literals interpreted as mathematical field
values. Binary modular power checks remain bounded; the qualified Lucas tree
is reused unchanged. Native compiler/library/caller binding is separate. -/

theorem checked_lucas_certificate_derives_exact_generator_order
    (certificate : Certificate)
    (primes : ∀ entry ∈ certificate.powers, Nat.Prime entry.factor)
    (checked : certificate.check = true) :
    orderOf (certificate.base : ZMod certificate.n) = certificate.n - 1 := by
  have facts : 1 < certificate.n ∧
      (certificate.powers.map FactorPower.factor).prod = certificate.n - 1 ∧
      ModularPower.power certificate.n certificate.base (certificate.n - 1) = 1 ∧
      ∀ entry ∈ certificate.powers, entry.check certificate.n certificate.base = true := by
    simpa [Certificate.check, Bool.and_eq_true, List.all_eq_true, and_assoc] using checked
  apply orderOf_eq_of_pow_and_pow_div_prime (by omega)
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

theorem exact_source_generator_has_full_multiplicative_field_order :
    orderOf (montgomeryValue (sourceConstantWords .generator) : ZMod nullifierModulus) = nullifierModulus - 1 := by
  rw [source_public_two_inverse_generator_and_root_inverse_have_exact_integer_values.2.1]
  change orderOf (FieldPrimeNode38.certificate.base : ZMod FieldPrimeNode38.certificate.n) = FieldPrimeNode38.certificate.n - 1
  apply checked_lucas_certificate_derives_exact_generator_order FieldPrimeNode38.certificate _ FieldPrimeNode38.checked
  simp [FieldPrimeNode38.certificate, FieldPrimeNode01.prime, FieldPrimeNode02.prime,
    FieldPrimeNode05.prime, FieldPrimeNode08.prime, FieldPrimeNode23.prime, FieldPrimeNode28.prime,
    FieldPrimeNode30.prime, FieldPrimeNode31.prime, FieldPrimeNode32.prime, FieldPrimeNode33.prime,
    FieldPrimeNode35.prime, FieldPrimeNode37.prime]

theorem exact_public_root_delta_and_inverse_binary_power_checks :
    ModularPower.power nullifierModulus 7 ((nullifierModulus - 1) / 2^32) =
      montgomeryValue (sourceConstantWords .rootOfUnity) ∧
    ModularPower.power nullifierModulus 7 (2^32) =
      montgomeryValue (sourceConstantWords .delta) ∧
    ModularPower.power nullifierModulus (montgomeryValue (sourceConstantWords .rootOfUnity)) (2^32) = 1 ∧
    ModularPower.power nullifierModulus (montgomeryValue (sourceConstantWords .rootOfUnity)) (2^31) ≠ 1 ∧
    ModularPower.power nullifierModulus (montgomeryValue (sourceConstantWords .rootOfUnityInverse)) (2^32) = 1 ∧
    ModularPower.power nullifierModulus (montgomeryValue (sourceConstantWords .rootOfUnityInverse)) (2^31) ≠ 1 := by
  decide +kernel

theorem exact_source_root_and_delta_are_the_generator_powers :
    (montgomeryValue (sourceConstantWords .rootOfUnity) : ZMod nullifierModulus) =
      (montgomeryValue (sourceConstantWords .generator) : ZMod nullifierModulus) ^ ((nullifierModulus - 1) / 2^32) ∧
    (montgomeryValue (sourceConstantWords .delta) : ZMod nullifierModulus) =
      (montgomeryValue (sourceConstantWords .generator) : ZMod nullifierModulus) ^ (2^32) := by
  rw [source_public_two_inverse_generator_and_root_inverse_have_exact_integer_values.2.1]
  constructor
  · rw [← ModularPower.power_sound, exact_public_root_delta_and_inverse_binary_power_checks.1]
  · rw [← ModularPower.power_sound, exact_public_root_delta_and_inverse_binary_power_checks.2.1]

theorem binary_power_and_half_nonidentity_derive_exact_two_power_order
    (value : ZMod nullifierModulus) (full : value ^ (2^32) = 1) (half : value ^ (2^31) ≠ 1) :
    orderOf value = 2^32 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) full
  intro q prime divides
  have qDividesTwo : q ∣ 2 := prime.dvd_of_dvd_pow divides
  have qEqualsTwo : q = 2 := Nat.le_antisymm (Nat.le_of_dvd (by decide) qDividesTwo) prime.two_le
  subst q
  exact half

theorem exact_source_root_and_inverse_have_order_two_to_the_thirty_two :
    orderOf (montgomeryValue (sourceConstantWords .rootOfUnity) : ZMod nullifierModulus) = 2^32 ∧
    orderOf (montgomeryValue (sourceConstantWords .rootOfUnityInverse) : ZMod nullifierModulus) = 2^32 := by
  constructor
  · apply binary_power_and_half_nonidentity_derive_exact_two_power_order
    · exact ModularPower.power_eq_one _ _ _ exact_public_root_delta_and_inverse_binary_power_checks.2.2.1
    · exact ModularPower.power_ne_one _ _ _ (by decide) exact_public_root_delta_and_inverse_binary_power_checks.2.2.2.1
  · apply binary_power_and_half_nonidentity_derive_exact_two_power_order
    · exact ModularPower.power_eq_one _ _ _ exact_public_root_delta_and_inverse_binary_power_checks.2.2.2.2.1
    · exact ModularPower.power_ne_one _ _ _ (by decide) exact_public_root_delta_and_inverse_binary_power_checks.2.2.2.2.2

theorem exact_source_delta_has_the_full_odd_part_field_order :
    orderOf (montgomeryValue (sourceConstantWords .delta) : ZMod nullifierModulus) =
      (nullifierModulus - 1) / 2^32 ∧ Odd ((nullifierModulus - 1) / 2^32) := by
  constructor
  · rw [exact_source_root_and_delta_are_the_generator_powers.2, orderOf_pow' (montgomeryValue (sourceConstantWords .generator) : ZMod nullifierModulus) (by decide : (2^32 : Nat) ≠ 0),
      exact_source_generator_has_full_multiplicative_field_order]
    congr 1
  · decide

set_option pp.all true in
#check @checked_lucas_certificate_derives_exact_generator_order
#print axioms checked_lucas_certificate_derives_exact_generator_order
set_option pp.all true in
#check @exact_source_generator_has_full_multiplicative_field_order
#print axioms exact_source_generator_has_full_multiplicative_field_order
set_option pp.all true in
#check @exact_public_root_delta_and_inverse_binary_power_checks
#print axioms exact_public_root_delta_and_inverse_binary_power_checks
set_option pp.all true in
#check @exact_source_root_and_delta_are_the_generator_powers
#print axioms exact_source_root_and_delta_are_the_generator_powers
set_option pp.all true in
#check @binary_power_and_half_nonidentity_derive_exact_two_power_order
#print axioms binary_power_and_half_nonidentity_derive_exact_two_power_order
set_option pp.all true in
#check @exact_source_root_and_inverse_have_order_two_to_the_thirty_two
#print axioms exact_source_root_and_inverse_have_order_two_to_the_thirty_two
set_option pp.all true in
#check @exact_source_delta_has_the_full_odd_part_field_order
#print axioms exact_source_delta_has_the_full_odd_part_field_order
end ShielddSecurity.TransferScalarPublicOrders01
