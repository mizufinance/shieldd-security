import ShielddSecurity.TransferScalarCanonicalDecoder01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarCanonicalKey01
open TransferScalarLittleEndianBytes01 (encodeLE decodeLE serializerBytes scalarKey)
open TransferScalarCanonicalDecoder01 (byteDecoderPayload sourceDecodeOption)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Construct every canonical mathematical nullifier key using exact typed
LE bytes and the actual modeled R2 decoder payload. No chosen desired raw
Montgomery state or arbitrary inverse codec is supplied. Projection, actual
source modeled decoder success, exact bytes and global canonical raw-vector
inverse derive. Native private Scalar/type/compiler/primitive/Choice/CtOption
and collection/trace bindings remain explicit; no native/certification credit. -/

def naturalKeyBytes (value : Nat) : Vector UInt8 32 :=
  ⟨(encodeLE 32 value).toArray, by
    rw [List.size_toArray]
    exact TransferScalarLittleEndianBytes01.typed_little_endian_encoding_has_exact_width 32 value⟩

def canonicalScalarForKey (key : Fin nullifierModulus) : CanonicalScalar :=
  ⟨byteDecoderPayload (naturalKeyBytes key.val),
    (TransferScalarCanonicalDecoder01.source_byte_decoder_payload_has_derived_range_and_serialized_value (naturalKeyBytes key.val)).1⟩

theorem canonical_natural_key_bytes_decode_to_exact_key (key : Fin nullifierModulus) :
    decodeLE (naturalKeyBytes key.val).toList = key.val := by
  change decodeLE (encodeLE 32 key.val).toArray.toList = _
  rw [List.toList_toArray]
  exact TransferScalarLittleEndianBytes01.typed_little_endian_encoding_reconstructs_bounded_integer
    32 key.val (Nat.lt_trans key.isLt (by decide : nullifierModulus < 256 ^ 32))

theorem constructed_source_scalar_projects_to_exact_canonical_key (key : Fin nullifierModulus) :
    scalarKey (canonicalScalarForKey key).words = key.val := by
  have value := (TransferScalarCanonicalDecoder01.source_byte_decoder_payload_has_derived_range_and_serialized_value
    (naturalKeyBytes key.val)).2
  rw [canonical_natural_key_bytes_decode_to_exact_key key, Nat.mod_eq_of_lt key.isLt] at value
  exact value

theorem constructed_source_scalar_serializes_to_exact_natural_key_bytes (key : Fin nullifierModulus) :
    serializerBytes (canonicalScalarForKey key).words.toList = (naturalKeyBytes key.val).toList := by
  have canonical : decodeLE (naturalKeyBytes key.val).toList < nullifierModulus := by
    rw [canonical_natural_key_bytes_decode_to_exact_key]; exact key.isLt
  exact (TransferScalarCanonicalDecoder01.accepted_canonical_bytes_decode_and_reserialize_exactly
    (naturalKeyBytes key.val) canonical).2

theorem actual_modeled_decoder_constructs_canonical_scalar_from_key_bytes (key : Fin nullifierModulus) :
    sourceDecodeOption (naturalKeyBytes key.val) = some (canonicalScalarForKey key).words := by
  have canonical : decodeLE (naturalKeyBytes key.val).toList < nullifierModulus := by
    rw [canonical_natural_key_bytes_decode_to_exact_key]; exact key.isLt
  exact (TransferScalarCanonicalDecoder01.accepted_canonical_bytes_decode_and_reserialize_exactly
    (naturalKeyBytes key.val) canonical).1

theorem canonical_source_key_constructor_recovers_every_canonical_raw_vector (scalar : CanonicalScalar) :
    (canonicalScalarForKey ⟨scalarKey scalar.words,
      TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical scalar.words⟩).words = scalar.words := by
  let key : Fin nullifierModulus := ⟨scalarKey scalar.words,
    TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical scalar.words⟩
  have projection := constructed_source_scalar_projects_to_exact_canonical_key key
  have same : TransferScalarMontgomeryValue01.montgomeryValue (canonicalScalarForKey key).words =
      TransferScalarMontgomeryValue01.montgomeryValue scalar.words := by
    rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value,
      ← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
    exact projection
  exact (TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal
    (canonicalScalarForKey key) scalar).mp same

theorem constructed_canonical_raw_vectors_are_equal_exactly_when_natural_keys_are_equal
    (left right : Fin nullifierModulus) :
    (canonicalScalarForKey left).words = (canonicalScalarForKey right).words ↔ left = right := by
  constructor
  · intro same
    have values := congrArg scalarKey same
    rw [constructed_source_scalar_projects_to_exact_canonical_key,
      constructed_source_scalar_projects_to_exact_canonical_key] at values
    exact Fin.ext values
  · intro same; rw [same]

set_option pp.all true in
#check @naturalKeyBytes
#print axioms naturalKeyBytes
set_option pp.all true in
#check @canonicalScalarForKey
#print axioms canonicalScalarForKey
set_option pp.all true in
#check @canonical_natural_key_bytes_decode_to_exact_key
#print axioms canonical_natural_key_bytes_decode_to_exact_key
set_option pp.all true in
#check @constructed_source_scalar_projects_to_exact_canonical_key
#print axioms constructed_source_scalar_projects_to_exact_canonical_key
set_option pp.all true in
#check @constructed_source_scalar_serializes_to_exact_natural_key_bytes
#print axioms constructed_source_scalar_serializes_to_exact_natural_key_bytes
set_option pp.all true in
#check @actual_modeled_decoder_constructs_canonical_scalar_from_key_bytes
#print axioms actual_modeled_decoder_constructs_canonical_scalar_from_key_bytes
set_option pp.all true in
#check @canonical_source_key_constructor_recovers_every_canonical_raw_vector
#print axioms canonical_source_key_constructor_recovers_every_canonical_raw_vector
set_option pp.all true in
#check @constructed_canonical_raw_vectors_are_equal_exactly_when_natural_keys_are_equal
#print axioms constructed_canonical_raw_vectors_are_equal_exactly_when_natural_keys_are_equal
end ShielddSecurity.TransferScalarCanonicalKey01
