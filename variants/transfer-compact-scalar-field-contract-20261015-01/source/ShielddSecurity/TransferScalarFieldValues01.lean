import ShielddSecurity.TransferScalarMontgomeryValue01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarFieldValues01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarMontgomeryValue01 (radixInverse)
open TransferBoundedNativeCodec01 (nullifierModulus)

theorem canonical_montgomery_word_contract_derives_exact_field_product
    (left right output : Nat) (canonical : output < nullifierModulus)
    (relation : (radix64 ^ 4 * output) % nullifierModulus = (left * right) % nullifierModulus) :
    (radixInverse * output) % nullifierModulus =
      ((radixInverse * left) % nullifierModulus * ((radixInverse * right) % nullifierModulus)) % nullifierModulus := by
  have scaled := congrArg (fun value : Nat => radixInverse * value % nullifierModulus) relation
  dsimp only at scaled
  simp only [Nat.mul_mod_mod] at scaled
  rw [← Nat.mul_assoc, Nat.mul_mod, TransferScalarMontgomeryValue01.source_four_word_radix_inverse_is_exact,
    Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt canonical] at scaled
  rw [scaled, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_mod_mod]
  apply congrArg (fun value : Nat => value % nullifierModulus)
  ac_rfl

set_option pp.all true in
#check @canonical_montgomery_word_contract_derives_exact_field_product
#print axioms canonical_montgomery_word_contract_derives_exact_field_product
end ShielddSecurity.TransferScalarFieldValues01
