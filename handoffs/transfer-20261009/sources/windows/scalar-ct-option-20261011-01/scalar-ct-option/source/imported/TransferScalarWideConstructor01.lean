import ShielddSecurity.TransferScalarProgramInvariant01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarWideConstructor01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarMontgomeryValue01 (radixInverse montgomeryValue)
open TransferScalarWideReduction01 (sourceMulMontgomery)
open TransferScalarR2Payload01 (sourceDecoderPayload)
open TransferScalarCanonicalAdd01 (sourceAddWords)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Pinned from_u512 splits eight words into two four-word digits, multiplies
the low digit by R2 and high digit by R3, then adds. Both raw digits may be
arbitrary. Actual multiplication/addition models derive a canonical payload
and serialization of the complete wide integer modulo p. Native eight LE
reads/word-index split/private Scalar/compiler/caller correspondence is separate. -/

def sourceR3 : Vector UInt64 4 :=
  #v[0xc62c1807439b73af, 0x1b3e0d188cf06990, 0x73d13c71c7b5f418, 0x6e2a5bb9c8db33e9]

theorem pinned_R3_words_have_exact_value_range_and_inverse_relation :
    packWords sourceR3.toList = (radix64 ^ 4) ^ 3 % nullifierModulus ∧
      packWords sourceR3.toList < nullifierModulus ∧
      (radixInverse * packWords sourceR3.toList) % nullifierModulus = (radix64 ^ 4) ^ 2 % nullifierModulus := by decide

def sourceHighPayload (raw : Vector UInt64 4) : Vector UInt64 4 :=
  ⟨(sourceMulMontgomery raw sourceR3).toArray, by
    rw [List.size_toArray]
    exact (TransferScalarWideReduction01.canonical_right_operand_source_multiplication_has_derived_montgomery_contract
      raw sourceR3 pinned_R3_words_have_exact_value_range_and_inverse_relation.2.1).1⟩

theorem high_digit_payload_has_derived_canonical_raw_montgomery_value (raw : Vector UInt64 4) :
    packWords (sourceHighPayload raw).toList < nullifierModulus ∧
      packWords (sourceHighPayload raw).toList = packWords raw.toList * (radix64 ^ 4) ^ 2 % nullifierModulus := by
  have contract := TransferScalarWideReduction01.canonical_right_operand_source_multiplication_has_derived_montgomery_contract
    raw sourceR3 pinned_R3_words_have_exact_value_range_and_inverse_relation.2.1
  have actual : (sourceHighPayload raw).toList = sourceMulMontgomery raw sourceR3 := List.toList_toArray
  rw [← actual] at contract
  have scaled := congrArg (fun value => radixInverse * value % nullifierModulus) contract.2.2
  dsimp only at scaled
  simp only [Nat.mul_mod_mod] at scaled
  rw [← Nat.mul_assoc, Nat.mul_mod, TransferScalarMontgomeryValue01.source_four_word_radix_inverse_is_exact,
    Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt contract.2.1] at scaled
  have reassoc : radixInverse * (packWords raw.toList * packWords sourceR3.toList) =
      packWords raw.toList * (radixInverse * packWords sourceR3.toList) := by ac_rfl
  rw [reassoc, Nat.mul_mod, pinned_R3_words_have_exact_value_range_and_inverse_relation.2.2,
    ← Nat.mul_mod] at scaled
  exact ⟨contract.2.1, scaled⟩

def sourceWidePayload (low high : Vector UInt64 4) : Vector UInt64 4 :=
  let l : CanonicalScalar := ⟨sourceDecoderPayload low,
    (TransferScalarR2Payload01.decoder_payload_has_derived_canonical_raw_montgomery_value low).1⟩
  let h : CanonicalScalar := ⟨sourceHighPayload high,
    (high_digit_payload_has_derived_canonical_raw_montgomery_value high).1⟩
  ⟨(sourceAddWords l.words h.words).toArray, by
    rw [List.size_toArray]
    exact (TransferScalarCanonicalAdd01.source_four_adc_and_modulus_sub_preserve_canonical_modular_sum l h).1⟩

theorem arbitrary_wide_digits_derive_canonical_payload_and_exact_whole_integer_key (low high : Vector UInt64 4) :
    packWords (sourceWidePayload low high).toList < nullifierModulus ∧
      scalarKey (sourceWidePayload low high) =
        (packWords low.toList + radix64 ^ 4 * packWords high.toList) % nullifierModulus := by
  let l : CanonicalScalar := ⟨sourceDecoderPayload low,
    (TransferScalarR2Payload01.decoder_payload_has_derived_canonical_raw_montgomery_value low).1⟩
  let h : CanonicalScalar := ⟨sourceHighPayload high,
    (high_digit_payload_has_derived_canonical_raw_montgomery_value high).1⟩
  have actual : (sourceWidePayload low high).toList = sourceAddWords l.words h.words := List.toList_toArray
  have contract := TransferScalarCanonicalAdd01.source_four_adc_and_modulus_sub_preserve_canonical_modular_sum l h
  rw [← actual] at contract
  have lowValue : packWords l.words.toList = packWords low.toList * radix64 ^ 4 % nullifierModulus :=
    (TransferScalarR2Payload01.decoder_payload_has_derived_canonical_raw_montgomery_value low).2
  have highValue : packWords h.words.toList = packWords high.toList * (radix64 ^ 4) ^ 2 % nullifierModulus :=
    (high_digit_payload_has_derived_canonical_raw_montgomery_value high).2
  have combined : (packWords l.words.toList + packWords h.words.toList) % nullifierModulus =
      ((packWords low.toList + radix64 ^ 4 * packWords high.toList) * radix64 ^ 4) % nullifierModulus := by
    rw [lowValue, highValue, ← Nat.add_mod]
    apply congrArg (fun value : Nat => value % nullifierModulus)
    rw [Nat.pow_two, Nat.add_mul]
    ac_rfl
  refine ⟨contract.2.1, ?_⟩
  rw [TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
  unfold montgomeryValue
  rw [contract.2.2, combined, Nat.mul_mod_mod]
  have reassoc : radixInverse * ((packWords low.toList + radix64 ^ 4 * packWords high.toList) * radix64 ^ 4) =
      (radixInverse * radix64 ^ 4) * (packWords low.toList + radix64 ^ 4 * packWords high.toList) := by ac_rfl
  rw [reassoc, Nat.mul_mod, TransferScalarMontgomeryValue01.source_four_word_radix_inverse_is_exact,
    Nat.one_mul, Nat.mod_mod]

set_option pp.all true in
#check @sourceR3
#print axioms sourceR3
set_option pp.all true in
#check @pinned_R3_words_have_exact_value_range_and_inverse_relation
#print axioms pinned_R3_words_have_exact_value_range_and_inverse_relation
set_option pp.all true in
#check @sourceHighPayload
#print axioms sourceHighPayload
set_option pp.all true in
#check @high_digit_payload_has_derived_canonical_raw_montgomery_value
#print axioms high_digit_payload_has_derived_canonical_raw_montgomery_value
set_option pp.all true in
#check @sourceWidePayload
#print axioms sourceWidePayload
set_option pp.all true in
#check @arbitrary_wide_digits_derive_canonical_payload_and_exact_whole_integer_key
#print axioms arbitrary_wide_digits_derive_canonical_payload_and_exact_whole_integer_key
end ShielddSecurity.TransferScalarWideConstructor01
