import ShielddSecurity.TransferScalarWideConstructor01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarWideByteInput01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarLittleEndianBytes01 (decodeLE scalarKey serializerBytes)
open TransferScalarByteDecode01 (decodeLEWords)
open TransferScalarWideConstructor01 (sourceWidePayload)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Source from_bytes_wide reads eight consecutive eight-byte LE words and
passes their two four-word digits to from_u512. The symbolic byte decoder
derives the exact full512-bit integer, then the actual wide constructor model
derives a canonical field and original-byte modular key. Native byte reads,
index/slice/array/library/compiler/caller binding remains separate. -/

def sourceWideByteDigits (bytes : Vector UInt8 64) : Vector UInt64 4 × Vector UInt64 4 :=
  (⟨(decodeLEWords 4 (bytes.toList.take 32)).toArray, by
    rw [List.size_toArray]
    exact TransferScalarByteDecode01.decoded_word_list_has_exact_requested_width 4 _⟩,
   ⟨(decodeLEWords 4 (bytes.toList.drop 32)).toArray, by
    rw [List.size_toArray]
    exact TransferScalarByteDecode01.decoded_word_list_has_exact_requested_width 4 _⟩)

def sourceFromWideBytes (bytes : Vector UInt8 64) : Vector UInt64 4 :=
  sourceWidePayload (sourceWideByteDigits bytes).1 (sourceWideByteDigits bytes).2

theorem source_eight_le_reads_reconstruct_the_exact_original_64_byte_integer (bytes : Vector UInt8 64) :
    packWords (sourceWideByteDigits bytes).1.toList + radix64 ^ 4 * packWords (sourceWideByteDigits bytes).2.toList =
      decodeLE bytes.toList := by
  have lowWidth : (bytes.toList.take 32).length = 32 := by
    rw [List.length_take, Vector.length_toList]; rfl
  have highWidth : (bytes.toList.drop 32).length = 32 := by
    rw [List.length_drop, Vector.length_toList]; rfl
  change packWords (decodeLEWords 4 (bytes.toList.take 32)).toArray.toList +
    radix64 ^ 4 * packWords (decodeLEWords 4 (bytes.toList.drop 32)).toArray.toList = _
  rw [List.toList_toArray, List.toList_toArray,
    TransferScalarByteDecode01.full_width_word_decoder_reconstructs_exact_little_endian_value 4 _ lowWidth,
    TransferScalarByteDecode01.full_width_word_decoder_reconstructs_exact_little_endian_value 4 _ highWidth]
  have joined := TransferScalarLittleEndianBytes01.little_endian_append_preserves_positional_value
    (bytes.toList.take 32) (bytes.toList.drop 32)
  rw [List.take_append_drop, lowWidth, (by decide : 256 ^ 32 = radix64 ^ 4)] at joined
  exact joined.symm

theorem arbitrary_64_source_bytes_derive_canonical_field_and_exact_modular_key (bytes : Vector UInt8 64) :
    packWords (sourceFromWideBytes bytes).toList < nullifierModulus ∧
      scalarKey (sourceFromWideBytes bytes) = decodeLE bytes.toList % nullifierModulus ∧
      (serializerBytes (sourceFromWideBytes bytes).toList).length = 32 := by
  have contract := TransferScalarWideConstructor01.arbitrary_wide_digits_derive_canonical_payload_and_exact_whole_integer_key
    (sourceWideByteDigits bytes).1 (sourceWideByteDigits bytes).2
  refine ⟨contract.1, ?_, ?_⟩
  · change scalarKey (sourceWidePayload (sourceWideByteDigits bytes).1 (sourceWideByteDigits bytes).2) = _
    rw [contract.2, source_eight_le_reads_reconstruct_the_exact_original_64_byte_integer]
  · exact TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width _ Vector.length_toList

set_option pp.all true in
#check @sourceWideByteDigits
#print axioms sourceWideByteDigits
set_option pp.all true in
#check @sourceFromWideBytes
#print axioms sourceFromWideBytes
set_option pp.all true in
#check @source_eight_le_reads_reconstruct_the_exact_original_64_byte_integer
#print axioms source_eight_le_reads_reconstruct_the_exact_original_64_byte_integer
set_option pp.all true in
#check @arbitrary_64_source_bytes_derive_canonical_field_and_exact_modular_key
#print axioms arbitrary_64_source_bytes_derive_canonical_field_and_exact_modular_key
end ShielddSecurity.TransferScalarWideByteInput01
