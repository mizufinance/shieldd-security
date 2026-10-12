import ShielddSecurity.TransferScalarR2Payload01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarCanonicalDecoder01
open TransferScalarByteDecode01 (decodeLEWords)
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes scalarKey)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarChoiceBit01 (sourceCanonicalChoiceByte)
open TransferScalarR2Payload01 (sourceDecoderPayload)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Construct the finite source decoder from four typed LE reads, the actual
modeled R2 multiplication payload, and the proved low borrow choice byte.
Option represents the documented success projection only. Accepted input
bytes roundtrip exactly; serializing a canonical raw Scalar then decoding
recovers its raw vector. Private Scalar invariants and native Choice/CtOption,
compiler/primitive/full execution correspondence remain explicit interfaces. -/

def parsedRawWords (bytes : Vector UInt8 32) : Vector UInt64 4 :=
  ⟨(decodeLEWords 4 bytes.toList).toArray, by
    rw [List.size_toArray]
    exact TransferScalarByteDecode01.decoded_word_list_has_exact_requested_width 4 bytes.toList⟩

def byteDecoderPayload (bytes : Vector UInt8 32) : Vector UInt64 4 :=
  sourceDecoderPayload (parsedRawWords bytes)

def sourceDecodeOption (bytes : Vector UInt8 32) : Option (Vector UInt64 4) :=
  let payload := byteDecoderPayload bytes
  if sourceCanonicalChoiceByte bytes = 1 then some payload else none

theorem parsed_four_raw_words_reconstruct_exact_input_bytes (bytes : Vector UInt8 32) :
    packWords (parsedRawWords bytes).toList = decodeLE bytes.toList := by
  change packWords (decodeLEWords 4 bytes.toList).toArray.toList = _
  rw [List.toList_toArray]
  exact TransferScalarByteDecode01.full_width_word_decoder_reconstructs_exact_little_endian_value
    4 bytes.toList Vector.length_toList

theorem source_byte_decoder_payload_has_derived_range_and_serialized_value (bytes : Vector UInt8 32) :
    packWords (byteDecoderPayload bytes).toList < nullifierModulus ∧
      scalarKey (byteDecoderPayload bytes) = decodeLE bytes.toList % nullifierModulus := by
  constructor
  · exact (TransferScalarR2Payload01.decoder_payload_has_derived_canonical_raw_montgomery_value (parsedRawWords bytes)).1
  · rw [byteDecoderPayload, TransferScalarR2Payload01.actual_modeled_decoder_payload_serializer_returns_raw_modulus_value,
      parsed_four_raw_words_reconstruct_exact_input_bytes]

theorem source_decoder_success_projection_accepts_exactly_canonical_bytes (bytes : Vector UInt8 32) :
    (∃ payload, sourceDecodeOption bytes = some payload) ↔ decodeLE bytes.toList < nullifierModulus := by
  have choice := TransferScalarChoiceBit01.source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus bytes
  constructor
  · rintro ⟨payload, decoded⟩
    by_cases yes : sourceCanonicalChoiceByte bytes = 1
    · exact choice.mp yes
    · rw [sourceDecodeOption, if_neg yes] at decoded
      cases decoded
  · intro canonical
    refine ⟨byteDecoderPayload bytes, ?_⟩
    rw [sourceDecodeOption, if_pos (choice.mpr canonical)]

theorem accepted_canonical_bytes_decode_and_reserialize_exactly
    (bytes : Vector UInt8 32) (canonical : decodeLE bytes.toList < nullifierModulus) :
    sourceDecodeOption bytes = some (byteDecoderPayload bytes) ∧
      serializerBytes (byteDecoderPayload bytes).toList = bytes.toList := by
  constructor
  · rw [sourceDecodeOption, if_pos
      ((TransferScalarChoiceBit01.source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus bytes).mpr canonical)]
  · apply TransferScalarByteEquality01.typed_little_endian_decoder_is_injective_at_equal_width
    · rw [TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width _ Vector.length_toList,
        Vector.length_toList]
    · change scalarKey (byteDecoderPayload bytes) = decodeLE bytes.toList
      rw [(source_byte_decoder_payload_has_derived_range_and_serialized_value bytes).2, Nat.mod_eq_of_lt canonical]

theorem canonical_raw_scalar_source_serialization_decodes_to_original_raw_vector
    (scalar : CanonicalScalar) (bytes : Vector UInt8 32) (encoded : bytes.toList = serializerBytes scalar.words.toList) :
    sourceDecodeOption bytes = some scalar.words := by
  have canonical : decodeLE bytes.toList < nullifierModulus := by
    rw [encoded]
    exact TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical scalar.words
  have roundtrip := accepted_canonical_bytes_decode_and_reserialize_exactly bytes canonical
  let restored : CanonicalScalar := ⟨byteDecoderPayload bytes,
    (source_byte_decoder_payload_has_derived_range_and_serialized_value bytes).1⟩
  have same : restored.words = scalar.words :=
    (TransferCanonicalWordEquality01.canonical_internal_source_bytes_equal_iff_raw_words_equal restored scalar).mp
      (roundtrip.2.trans encoded)
  change byteDecoderPayload bytes = scalar.words at same
  rw [roundtrip.1, same]

set_option pp.all true in
#check @parsedRawWords
#print axioms parsedRawWords
set_option pp.all true in
#check @byteDecoderPayload
#print axioms byteDecoderPayload
set_option pp.all true in
#check @sourceDecodeOption
#print axioms sourceDecodeOption
set_option pp.all true in
#check @parsed_four_raw_words_reconstruct_exact_input_bytes
#print axioms parsed_four_raw_words_reconstruct_exact_input_bytes
set_option pp.all true in
#check @source_byte_decoder_payload_has_derived_range_and_serialized_value
#print axioms source_byte_decoder_payload_has_derived_range_and_serialized_value
set_option pp.all true in
#check @source_decoder_success_projection_accepts_exactly_canonical_bytes
#print axioms source_decoder_success_projection_accepts_exactly_canonical_bytes
set_option pp.all true in
#check @accepted_canonical_bytes_decode_and_reserialize_exactly
#print axioms accepted_canonical_bytes_decode_and_reserialize_exactly
set_option pp.all true in
#check @canonical_raw_scalar_source_serialization_decodes_to_original_raw_vector
#print axioms canonical_raw_scalar_source_serialization_decodes_to_original_raw_vector
end ShielddSecurity.TransferScalarCanonicalDecoder01
