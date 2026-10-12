import ShielddSecurity.TransferNullifierFieldCodec01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferNullifierFieldDomain01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarLittleEndianBytes01 (encodeLE decodeLE scalarKey serializerBytes)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferNullifierFieldCodec01 (sourceNullifierSliceDecode)
/-! Full modeled field-domain coverage, without assuming desired constructor
output. Every residue below the pinned BLS Scalar modulus is encoded into
32 finite bytes and sent through the qualified source R2 decoder payload.
Derived field meaning and exact serialization make this construction and
the source serializer projection mutual inverses on canonical raw fields.
This proves modeled domain coverage; Rust alias source association, private
constructor origins, native operations/compiler/ABI/callers remain separate.
No claims about Jubjub subgroup scalars, timing or full Transfer execution. -/

def canonicalResidueBytes (value : Fin nullifierModulus) : Vector UInt8 32 :=
  ⟨(encodeLE 32 value.val).toArray, by
    rw [List.size_toArray]
    exact TransferScalarLittleEndianBytes01.typed_little_endian_encoding_has_exact_width 32 value.val⟩

theorem every_field_residue_has_exact_32_byte_little_endian_value (value : Fin nullifierModulus) :
    decodeLE (canonicalResidueBytes value).toList = value.val := by
  change decodeLE (encodeLE 32 value.val).toArray.toList = value.val
  rw [List.toList_toArray]
  exact TransferScalarLittleEndianBytes01.typed_little_endian_encoding_reconstructs_bounded_integer
    32 value.val (Nat.lt_trans value.isLt (by decide : nullifierModulus < 256 ^ 32))

def sourceResidueField (value : Fin nullifierModulus) : CanonicalScalar :=
  ⟨TransferScalarCanonicalDecoder01.byteDecoderPayload (canonicalResidueBytes value),
    (TransferScalarCanonicalDecoder01.source_byte_decoder_payload_has_derived_range_and_serialized_value
      (canonicalResidueBytes value)).1⟩

theorem every_field_residue_encoding_returns_the_actual_source_decoder_payload (value : Fin nullifierModulus) :
    sourceNullifierSliceDecode (canonicalResidueBytes value).toList = some (sourceResidueField value) := by
  rw [sourceNullifierSliceDecode, dif_pos Vector.length_toList]
  have yes : TransferScalarChoiceBit01.sourceCanonicalChoiceByte (canonicalResidueBytes value) = 1 := by
    apply (TransferScalarChoiceBit01.source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus _).mpr
    rw [every_field_residue_has_exact_32_byte_little_endian_value]
    exact value.isLt
  change TransferScalarInputFamily01.sourceInputEval (.bytes (canonicalResidueBytes value)) = some (sourceResidueField value)
  rw [TransferScalarInputFamily01.sourceInputEval, if_pos yes]
  rfl

theorem actual_source_residue_constructor_has_the_exact_mathematical_field_value (value : Fin nullifierModulus) :
    montgomeryValue (sourceResidueField value).words = value.val := by
  have meaning := (TransferNullifierFieldCodec01.returned_source_nullifier_has_exact_input_field_value_and_bytes
    _ _ (every_field_residue_encoding_returns_the_actual_source_decoder_payload value)).1
  exact meaning.trans (every_field_residue_has_exact_32_byte_little_endian_value value)

def sourceFieldResidue (scalar : CanonicalScalar) : Fin nullifierModulus :=
  ⟨scalarKey scalar.words,
    TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical scalar.words⟩

theorem source_serializer_residue_projection_is_the_mathematical_field (scalar : CanonicalScalar) :
    (sourceFieldResidue scalar).val = montgomeryValue scalar.words := by
  dsimp only [sourceFieldResidue]
  exact TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value scalar.words

theorem source_residue_constructor_then_serializer_recovers_every_legal_residue (value : Fin nullifierModulus) :
    sourceFieldResidue (sourceResidueField value) = value := by
  apply Fin.ext
  exact (source_serializer_residue_projection_is_the_mathematical_field _).trans
    (actual_source_residue_constructor_has_the_exact_mathematical_field_value value)

theorem source_serializer_then_residue_constructor_recovers_every_canonical_raw_field (scalar : CanonicalScalar) :
    sourceResidueField (sourceFieldResidue scalar) = scalar := by
  have same : montgomeryValue (sourceResidueField (sourceFieldResidue scalar)).words = montgomeryValue scalar.words :=
    (actual_source_residue_constructor_has_the_exact_mathematical_field_value _).trans
      (source_serializer_residue_projection_is_the_mathematical_field scalar)
  exact TransferScalarChoiceMasks01.canonical_scalar_objects_equal_of_exact_raw_word_equality _ _
    ((TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal _ _).mp same)

theorem actual_source_decoder_covers_the_entire_legal_field_residue_domain (value : Fin nullifierModulus) :
    ∃ scalar : CanonicalScalar, sourceNullifierSliceDecode (canonicalResidueBytes value).toList = some scalar ∧
      montgomeryValue scalar.words = value.val := by
  exact ⟨sourceResidueField value,
    every_field_residue_encoding_returns_the_actual_source_decoder_payload value,
    actual_source_residue_constructor_has_the_exact_mathematical_field_value value⟩

theorem actual_source_residue_constructor_serializes_to_the_exact_original_residue_bytes (value : Fin nullifierModulus) :
    serializerBytes (sourceResidueField value).words.toList = (canonicalResidueBytes value).toList := by
  exact (TransferNullifierFieldCodec01.returned_source_nullifier_has_exact_input_field_value_and_bytes
    _ _ (every_field_residue_encoding_returns_the_actual_source_decoder_payload value)).2

set_option pp.all true in
#check @canonicalResidueBytes
#print axioms canonicalResidueBytes
set_option pp.all true in
#check @every_field_residue_has_exact_32_byte_little_endian_value
#print axioms every_field_residue_has_exact_32_byte_little_endian_value
set_option pp.all true in
#check @sourceResidueField
#print axioms sourceResidueField
set_option pp.all true in
#check @every_field_residue_encoding_returns_the_actual_source_decoder_payload
#print axioms every_field_residue_encoding_returns_the_actual_source_decoder_payload
set_option pp.all true in
#check @actual_source_residue_constructor_has_the_exact_mathematical_field_value
#print axioms actual_source_residue_constructor_has_the_exact_mathematical_field_value
set_option pp.all true in
#check @sourceFieldResidue
#print axioms sourceFieldResidue
set_option pp.all true in
#check @source_serializer_residue_projection_is_the_mathematical_field
#print axioms source_serializer_residue_projection_is_the_mathematical_field
set_option pp.all true in
#check @source_residue_constructor_then_serializer_recovers_every_legal_residue
#print axioms source_residue_constructor_then_serializer_recovers_every_legal_residue
set_option pp.all true in
#check @source_serializer_then_residue_constructor_recovers_every_canonical_raw_field
#print axioms source_serializer_then_residue_constructor_recovers_every_canonical_raw_field
set_option pp.all true in
#check @actual_source_decoder_covers_the_entire_legal_field_residue_domain
#print axioms actual_source_decoder_covers_the_entire_legal_field_residue_domain
set_option pp.all true in
#check @actual_source_residue_constructor_serializes_to_the_exact_original_residue_bytes
#print axioms actual_source_residue_constructor_serializes_to_the_exact_original_residue_bytes
end ShielddSecurity.TransferNullifierFieldDomain01
