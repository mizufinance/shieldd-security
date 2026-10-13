import ShielddSecurity.TransferScalarPredicates01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarPackChunk01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes)
open TransferScalarChoiceBit01 (sourceCanonicalChoiceByte)
open TransferScalarCanonicalDecoder01 (byteDecoderPayload)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Source encoding::pack chunk constructor: zero32-byte destination, copy
the at-most31-byte chunk into its prefix, Fq::from_bytes(...).unwrap().
The complete typed chunk domain derives canonical acceptance, stored R2
payload and exact original integer/zero-padded serialization. No desired
success or output premise is supplied. Native chunks(31)/slice-copy/index/
unwrap/compiler/ABI and callers remain explicit interfaces; this is not an
executed panic control or full Transfer/native certification. -/

theorem arbitrary_zero_padding_has_zero_little_endian_value (count : Nat) :
    decodeLE (List.replicate count (0 : UInt8)) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change 0 + 256 * decodeLE (List.replicate count (0 : UInt8)) = 0
    rw [ih]

def sourcePaddedChunkBytes (chunk : List UInt8) (width : chunk.length ≤ 31) : Vector UInt8 32 :=
  ⟨(chunk ++ List.replicate (32 - chunk.length) 0).toArray, by
    rw [List.size_toArray, List.length_append, List.length_replicate]
    omega⟩

theorem exact_source_padded_chunk_has_original_prefix_and_zero_suffix
    (chunk : List UInt8) (width : chunk.length ≤ 31) :
    (sourcePaddedChunkBytes chunk width).toList = chunk ++ List.replicate (32 - chunk.length) 0 := by
  exact List.toList_toArray

theorem exact_source_padding_preserves_the_original_chunk_integer
    (chunk : List UInt8) (width : chunk.length ≤ 31) :
    decodeLE (sourcePaddedChunkBytes chunk width).toList = decodeLE chunk := by
  rw [exact_source_padded_chunk_has_original_prefix_and_zero_suffix,
    TransferScalarLittleEndianBytes01.little_endian_append_preserves_positional_value,
    arbitrary_zero_padding_has_zero_little_endian_value, Nat.mul_zero, Nat.add_zero]

theorem every_at_most31_typed_byte_chunk_is_below_the_exact_field_modulus
    (chunk : List UInt8) (width : chunk.length ≤ 31) : decodeLE chunk < nullifierModulus := by
  have bounded := TransferScalarByteDecode01.typed_byte_decode_is_below_positional_width chunk
  have monotone : 256 ^ chunk.length ≤ 256 ^ 31 := Nat.pow_le_pow_right (by decide) width
  exact Nat.lt_trans (Nat.lt_of_lt_of_le bounded monotone) (by decide : 256 ^ 31 < nullifierModulus)

def sourcePackedChunkField (chunk : List UInt8) (width : chunk.length ≤ 31) : CanonicalScalar :=
  ⟨byteDecoderPayload (sourcePaddedChunkBytes chunk width),
    (TransferScalarCanonicalDecoder01.source_byte_decoder_payload_has_derived_range_and_serialized_value
      (sourcePaddedChunkBytes chunk width)).1⟩

theorem every_source_packed_chunk_derives_the_exact_success_choice_byte
    (chunk : List UInt8) (width : chunk.length ≤ 31) :
    sourceCanonicalChoiceByte (sourcePaddedChunkBytes chunk width) = 1 := by
  apply (TransferScalarChoiceBit01.source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus _).mpr
  rw [exact_source_padding_preserves_the_original_chunk_integer]
  exact every_at_most31_typed_byte_chunk_is_below_the_exact_field_modulus chunk width

theorem every_source_padded_chunk_decoder_returns_the_actual_canonical_payload
    (chunk : List UInt8) (width : chunk.length ≤ 31) :
    TransferNullifierFieldCodec01.sourceNullifierSliceDecode (sourcePaddedChunkBytes chunk width).toList =
      some (sourcePackedChunkField chunk width) := by
  rw [TransferNullifierFieldCodec01.sourceNullifierSliceDecode, dif_pos Vector.length_toList]
  change TransferScalarInputFamily01.sourceInputEval (.bytes (sourcePaddedChunkBytes chunk width)) =
    some (sourcePackedChunkField chunk width)
  rw [TransferScalarInputFamily01.sourceInputEval, if_pos (every_source_packed_chunk_derives_the_exact_success_choice_byte chunk width)]
  rfl

theorem every_source_packed_chunk_has_the_exact_original_mathematical_integer
    (chunk : List UInt8) (width : chunk.length ≤ 31) :
    montgomeryValue (sourcePackedChunkField chunk width).words = decodeLE chunk := by
  have meaning := (TransferNullifierFieldCodec01.returned_source_nullifier_has_exact_input_field_value_and_bytes
    _ _ (every_source_padded_chunk_decoder_returns_the_actual_canonical_payload chunk width)).1
  exact meaning.trans (exact_source_padding_preserves_the_original_chunk_integer chunk width)

theorem every_source_packed_chunk_serializes_to_the_exact_padded_original_bytes
    (chunk : List UInt8) (width : chunk.length ≤ 31) :
    serializerBytes (sourcePackedChunkField chunk width).words.toList =
      chunk ++ List.replicate (32 - chunk.length) 0 := by
  have bytes := (TransferNullifierFieldCodec01.returned_source_nullifier_has_exact_input_field_value_and_bytes
    _ _ (every_source_padded_chunk_decoder_returns_the_actual_canonical_payload chunk width)).2
  exact bytes.trans (exact_source_padded_chunk_has_original_prefix_and_zero_suffix chunk width)

set_option pp.all true in
#check @arbitrary_zero_padding_has_zero_little_endian_value
#print axioms arbitrary_zero_padding_has_zero_little_endian_value
set_option pp.all true in
#check @sourcePaddedChunkBytes
#print axioms sourcePaddedChunkBytes
set_option pp.all true in
#check @exact_source_padded_chunk_has_original_prefix_and_zero_suffix
#print axioms exact_source_padded_chunk_has_original_prefix_and_zero_suffix
set_option pp.all true in
#check @exact_source_padding_preserves_the_original_chunk_integer
#print axioms exact_source_padding_preserves_the_original_chunk_integer
set_option pp.all true in
#check @every_at_most31_typed_byte_chunk_is_below_the_exact_field_modulus
#print axioms every_at_most31_typed_byte_chunk_is_below_the_exact_field_modulus
set_option pp.all true in
#check @sourcePackedChunkField
#print axioms sourcePackedChunkField
set_option pp.all true in
#check @every_source_packed_chunk_derives_the_exact_success_choice_byte
#print axioms every_source_packed_chunk_derives_the_exact_success_choice_byte
set_option pp.all true in
#check @every_source_padded_chunk_decoder_returns_the_actual_canonical_payload
#print axioms every_source_padded_chunk_decoder_returns_the_actual_canonical_payload
set_option pp.all true in
#check @every_source_packed_chunk_has_the_exact_original_mathematical_integer
#print axioms every_source_packed_chunk_has_the_exact_original_mathematical_integer
set_option pp.all true in
#check @every_source_packed_chunk_serializes_to_the_exact_padded_original_bytes
#print axioms every_source_packed_chunk_serializes_to_the_exact_padded_original_bytes
end ShielddSecurity.TransferScalarPackChunk01
