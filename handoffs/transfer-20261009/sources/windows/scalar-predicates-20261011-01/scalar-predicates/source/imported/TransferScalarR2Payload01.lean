import ShielddSecurity.TransferScalarWideReduction01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarR2Payload01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarMontgomeryValue01 (radixInverse montgomeryValue)
open TransferScalarWideReduction01 (sourceMulMontgomery)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Exact pinned R2 words and actual modeled decoder multiplication payload.
The payload is constructed by source schoolbook MAC rows, wide Montgomery
MAC/ADC rounds, discarded-carry proof and masked subtraction. Canonical raw
payload and serialized input value are derived, not supplied as constructor
state. Native Choice/CtOption/private Scalar/compiler/primitive/full trace
binding remain explicit. This is arithmetic model proof, not native credit. -/

def sourceR2 : Vector UInt64 4 :=
  #v[0xc999e990f3f29c6d, 0x2b6cedcb87925c23, 0x05d314967254398f, 0x0748d9d99f59ff11]

theorem pinned_R2_words_have_exact_value_range_and_inverse_relation :
    packWords sourceR2.toList = (radix64 ^ 4) ^ 2 % nullifierModulus ∧
      packWords sourceR2.toList < nullifierModulus ∧
      (radixInverse * packWords sourceR2.toList) % nullifierModulus = radix64 ^ 4 % nullifierModulus := by decide

def sourceDecoderPayload (raw : Vector UInt64 4) : Vector UInt64 4 :=
  ⟨(sourceMulMontgomery raw sourceR2).toArray, by
    rw [List.size_toArray]
    exact (TransferScalarWideReduction01.canonical_right_operand_source_multiplication_has_derived_montgomery_contract
      raw sourceR2 pinned_R2_words_have_exact_value_range_and_inverse_relation.2.1).1⟩

theorem decoder_payload_words_are_actual_modeled_multiplication_output (raw : Vector UInt64 4) :
    (sourceDecoderPayload raw).toList = sourceMulMontgomery raw sourceR2 := by
  change (sourceMulMontgomery raw sourceR2).toArray.toList = _
  exact List.toList_toArray

theorem decoder_payload_has_derived_canonical_raw_montgomery_value (raw : Vector UInt64 4) :
    packWords (sourceDecoderPayload raw).toList < nullifierModulus ∧
      packWords (sourceDecoderPayload raw).toList = packWords raw.toList * radix64 ^ 4 % nullifierModulus := by
  have contract := TransferScalarWideReduction01.canonical_right_operand_source_multiplication_has_derived_montgomery_contract
    raw sourceR2 pinned_R2_words_have_exact_value_range_and_inverse_relation.2.1
  rw [← decoder_payload_words_are_actual_modeled_multiplication_output raw] at contract
  have scaled := congrArg (fun value => radixInverse * value % nullifierModulus) contract.2.2
  dsimp only at scaled
  simp only [Nat.mul_mod_mod] at scaled
  rw [← Nat.mul_assoc, Nat.mul_mod, TransferScalarMontgomeryValue01.source_four_word_radix_inverse_is_exact,
    Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt contract.2.1] at scaled
  have reassoc : radixInverse * (packWords raw.toList * packWords sourceR2.toList) =
      packWords raw.toList * (radixInverse * packWords sourceR2.toList) := by ac_rfl
  rw [reassoc, Nat.mul_mod, pinned_R2_words_have_exact_value_range_and_inverse_relation.2.2,
    ← Nat.mul_mod] at scaled
  exact ⟨contract.2.1, scaled⟩

theorem actual_modeled_decoder_payload_serializer_returns_raw_modulus_value (raw : Vector UInt64 4) :
    scalarKey (sourceDecoderPayload raw) = packWords raw.toList % nullifierModulus := by
  rw [TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
  unfold montgomeryValue
  rw [(decoder_payload_has_derived_canonical_raw_montgomery_value raw).2, Nat.mul_mod_mod]
  have reassoc : radixInverse * (packWords raw.toList * radix64 ^ 4) =
      (radixInverse * radix64 ^ 4) * packWords raw.toList := by ac_rfl
  rw [reassoc, Nat.mul_mod, TransferScalarMontgomeryValue01.source_four_word_radix_inverse_is_exact,
    Nat.one_mul, Nat.mod_mod]

theorem accepted_canonical_raw_payload_serializes_to_exact_input_value
    (raw : Vector UInt64 4) (canonical : packWords raw.toList < nullifierModulus) :
    scalarKey (sourceDecoderPayload raw) = packWords raw.toList := by
  rw [actual_modeled_decoder_payload_serializer_returns_raw_modulus_value, Nat.mod_eq_of_lt canonical]

set_option pp.all true in
#check @sourceR2
#print axioms sourceR2
set_option pp.all true in
#check @pinned_R2_words_have_exact_value_range_and_inverse_relation
#print axioms pinned_R2_words_have_exact_value_range_and_inverse_relation
set_option pp.all true in
#check @sourceDecoderPayload
#print axioms sourceDecoderPayload
set_option pp.all true in
#check @decoder_payload_words_are_actual_modeled_multiplication_output
#print axioms decoder_payload_words_are_actual_modeled_multiplication_output
set_option pp.all true in
#check @decoder_payload_has_derived_canonical_raw_montgomery_value
#print axioms decoder_payload_has_derived_canonical_raw_montgomery_value
set_option pp.all true in
#check @actual_modeled_decoder_payload_serializer_returns_raw_modulus_value
#print axioms actual_modeled_decoder_payload_serializer_returns_raw_modulus_value
set_option pp.all true in
#check @accepted_canonical_raw_payload_serializes_to_exact_input_value
#print axioms accepted_canonical_raw_payload_serializes_to_exact_input_value
end ShielddSecurity.TransferScalarR2Payload01
