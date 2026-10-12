import ShielddSecurity.TransferScalarExtendedFamily01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarFieldValues01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarMontgomeryValue01 (radixInverse montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarPowInvariant01 (sourceCanonicalMul sourceCanonicalSquare sourceRepeatedSquare)
/-! Recover mathematical field values from actual modeled Montgomery word
contracts. The already proved exact radix inverse removes the Montgomery
factor; symbolic modular algebra proves multiply, optimized square and any
repeated-square count. No unrolled field exponent or caller desired output
equation is used. Native compiler/caller correspondence remains separate. -/

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

theorem actual_modeled_canonical_multiply_has_exact_mathematical_field_value (left right : CanonicalScalar) :
    montgomeryValue (sourceCanonicalMul left right).words =
      (montgomeryValue left.words * montgomeryValue right.words) % nullifierModulus := by
  have actual : (sourceCanonicalMul left right).words.toList =
      TransferScalarWideReduction01.sourceMulMontgomery left.words right.words := by
    change (TransferScalarWideReduction01.sourceMulMontgomery left.words right.words).toArray.toList = _
    exact List.toList_toArray
  have contract := TransferScalarWideReduction01.canonical_right_operand_source_multiplication_has_derived_montgomery_contract
    left.words right.words right.canonical
  rw [← actual] at contract
  unfold montgomeryValue
  exact canonical_montgomery_word_contract_derives_exact_field_product _ _ _ contract.2.1 contract.2.2

theorem actual_modeled_canonical_optimized_square_has_exact_mathematical_field_value (value : CanonicalScalar) :
    montgomeryValue (sourceCanonicalSquare value).words =
      (montgomeryValue value.words * montgomeryValue value.words) % nullifierModulus := by
  have actual : (sourceCanonicalSquare value).words.toList =
      TransferScalarSquareProduct01.sourceSquareMontgomery value.words := by
    change (TransferScalarSquareProduct01.sourceSquareMontgomery value.words).toArray.toList = _
    exact List.toList_toArray
  have contract := TransferScalarSquareProduct01.canonical_operand_source_square_derives_canonical_montgomery_contract
    value.words value.canonical
  rw [← actual] at contract
  unfold montgomeryValue
  exact canonical_montgomery_word_contract_derives_exact_field_product _ _ _ contract.2.1 contract.2.2

theorem symbolic_repeated_source_optimized_square_has_exact_mathematical_field_power
    (count : Nat) (value : CanonicalScalar) :
    montgomeryValue (sourceRepeatedSquare count value).words =
      (montgomeryValue value.words) ^ (2 ^ count) % nullifierModulus := by
  induction count generalizing value with
  | zero =>
    change montgomeryValue value.words = (montgomeryValue value.words) ^ 1 % nullifierModulus
    rw [Nat.pow_one]
    unfold montgomeryValue
    rw [Nat.mod_mod]
  | succ count ih =>
    change montgomeryValue (sourceRepeatedSquare count (sourceCanonicalSquare value)).words = _
    rw [ih, actual_modeled_canonical_optimized_square_has_exact_mathematical_field_value,
      ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
    have exponent : 2 * 2 ^ count = 2 ^ (count + 1) := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [exponent]

set_option pp.all true in
#check @canonical_montgomery_word_contract_derives_exact_field_product
#print axioms canonical_montgomery_word_contract_derives_exact_field_product
set_option pp.all true in
#check @actual_modeled_canonical_multiply_has_exact_mathematical_field_value
#print axioms actual_modeled_canonical_multiply_has_exact_mathematical_field_value
set_option pp.all true in
#check @actual_modeled_canonical_optimized_square_has_exact_mathematical_field_value
#print axioms actual_modeled_canonical_optimized_square_has_exact_mathematical_field_value
set_option pp.all true in
#check @symbolic_repeated_source_optimized_square_has_exact_mathematical_field_power
#print axioms symbolic_repeated_source_optimized_square_has_exact_mathematical_field_power
end ShielddSecurity.TransferScalarFieldValues01
