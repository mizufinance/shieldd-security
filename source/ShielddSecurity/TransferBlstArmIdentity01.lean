import ShielddSecurity.TransferBlstArmCaller01
import ShielddSecurity.TransferScalarReversedByteOrder01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmIdentity01
open TransferBlstArmCaller01
open TransferBlstArmNormalized01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferScalarLittleEndianBytes01 (serializerBytes encodeLE decodeLE)
open TransferScalarReversedByteOrder01 (compareHighFirst)
attribute [local irreducible] Vector.ofFn sourceAsSlice sourceScalarFromFr sourceBendianFromScalar
  sourceArmFromMontVector TransferBlstByteCaller01.sourceScalarLEBytes64
  TransferBlstByteCaller01.sourceLEParseMemory64 TransferBlstEncoder01.sourceBEFromLimbs64
  serializerBytes montgomeryValue encodeLE decodeLE compareHighFirst sourceBlstFrWordMeaning

/-- The 32 bytes passed to Hasher::write and array Ord::cmp by the original
caller. Hash algorithm and collection implementation correspondence are separate. -/
def sourceCallerByteKey (memory : CallerMemory) (scratch : Vector UInt64 4) : List UInt8 :=
  (sourceAsSlice memory scratch).2.2.toList

attribute [local irreducible] sourceCallerByteKey

theorem source_caller_byte_key_has_exactly_32_bytes (memory : CallerMemory) (scratch : Vector UInt64 4) :
    (sourceCallerByteKey memory scratch).length = 32 := by
  rw [sourceCallerByteKey,Vector.length_toList]

theorem qualified_sdk_serializer_is_the_exact_bounded_integer_encoding (words : Vector UInt64 4) :
    serializerBytes words.toList = encodeLE 32 (montgomeryValue words) := by
  apply TransferScalarByteEquality01.typed_little_endian_decoder_is_injective_at_equal_width
  · rw [TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width _ Vector.length_toList,
      TransferScalarLittleEndianBytes01.typed_little_endian_encoding_has_exact_width]
  · have bound : montgomeryValue words < 256^32 := by
      have original : montgomeryValue words < TransferBoundedNativeCodec01.nullifierModulus := by
        rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
        exact TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical words
      exact Nat.lt_trans original (by decide)
    rw [TransferScalarLittleEndianBytes01.typed_little_endian_encoding_reconstructs_bounded_integer _ _ bound]
    exact TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value words

theorem reverse_integer_encoding_byte_is_the_exact_big_endian_quotient
    (value : Nat) (index : Fin 32) :
    ((encodeLE 32 value).reverse)[index.val]'(by
      rw [List.length_reverse,TransferScalarLittleEndianBytes01.typed_little_endian_encoding_has_exact_width]
      exact index.isLt) = UInt8.ofNat (value/256^(31-index.val) % 256) := by
  rw [List.getElem_reverse]
  simp only [TransferScalarLittleEndianBytes01.typed_little_endian_encoding_has_exact_width]
  exact TransferBlstByteRoundtrip01.symbolic_integer_le_encoder_index_is_the_exact_byte_quotient
    32 value (31-index.val) (by have := index.isLt; omega)

theorem original_caller_byte_key_is_exactly_the_qualified_reversed_sdk_encoding
    (memory : CallerMemory) (scratch : Vector UInt64 4) :
    sourceCallerByteKey memory scratch = (serializerBytes memory.1.toList).reverse := by
  rw [qualified_sdk_serializer_is_the_exact_bounded_integer_encoding]
  have numeric := actual_full_from_mont_output_derives_its_input_representation_field_value memory.1
  rw [actual_full_from_mont_fixed_vector_is_the_actual_four_output_words,
    actual_full_from_mont_source_program_derives_the_original_montgomery_value] at numeric
  apply List.ext_getElem
  · rw [source_caller_byte_key_has_exactly_32_bytes,List.length_reverse,
      TransferScalarLittleEndianBytes01.typed_little_endian_encoding_has_exact_width]
  · intro index leftBound rightBound
    have inside : index < 32 := by
      rw [source_caller_byte_key_has_exactly_32_bytes] at leftBound
      exact leftBound
    have actual : (sourceCallerByteKey memory scratch)[index]'leftBound =
        TransferCommonwareMapBytes01.canonicalBEByte (sourceBlstFrWordMeaning memory.1) ⟨index,inside⟩ := by
      simpa only [sourceCallerByteKey,Vector.getElem_toList] using
        caller_as_slice_derives_every_original_input_field_byte memory scratch ⟨index,inside⟩
    have encoded := reverse_integer_encoding_byte_is_the_exact_big_endian_quotient
      (montgomeryValue memory.1) ⟨index,inside⟩
    calc
      _ = TransferCommonwareMapBytes01.canonicalBEByte (sourceBlstFrWordMeaning memory.1) ⟨index,inside⟩ := actual
      _ = UInt8.ofNat (montgomeryValue memory.1/256^(31-index) % 256) := by
        simp only [TransferCommonwareMapBytes01.canonicalBEByte,← numeric]
      _ = _ := encoded.symm

def sourceCallerOrd (left right : CallerMemory) (leftScratch rightScratch : Vector UInt64 4) : Ordering :=
  compareHighFirst (sourceCallerByteKey left leftScratch) (sourceCallerByteKey right rightScratch)

theorem original_caller_array_comparison_derives_the_original_field_numeric_order
    (left right : CallerMemory) (leftScratch rightScratch : Vector UInt64 4) :
    sourceCallerOrd left right leftScratch rightScratch = compare (montgomeryValue left.1) (montgomeryValue right.1) := by
  rw [sourceCallerOrd,original_caller_byte_key_is_exactly_the_qualified_reversed_sdk_encoding,
    original_caller_byte_key_is_exactly_the_qualified_reversed_sdk_encoding]
  exact TransferScalarReversedByteOrder01.source_reversed_32_byte_comparison_is_exact_mathematical_montgomery_order _ _

theorem canonical_original_caller_hash_inputs_equal_iff_original_raw_words_equal
    (left right : CanonicalScalar) (leftScratch rightScratch : Vector UInt64 4)
    (leftScalar rightScalar leftOutput rightOutput : Vector UInt8 32) :
    sourceCallerByteKey (left.words,leftScalar,leftOutput) leftScratch =
      sourceCallerByteKey (right.words,rightScalar,rightOutput) rightScratch ↔ left.words = right.words := by
  rw [original_caller_byte_key_is_exactly_the_qualified_reversed_sdk_encoding,
    original_caller_byte_key_is_exactly_the_qualified_reversed_sdk_encoding,List.reverse_inj,
    TransferScalarByteEquality01.source_scalar_typed_byte_keys_equal_iff_mathematical_montgomery_values_equal]
  exact TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal left right

theorem canonical_original_caller_order_equality_agrees_with_original_raw_word_equality
    (left right : CanonicalScalar) (leftScratch rightScratch : Vector UInt64 4)
    (leftScalar rightScalar leftOutput rightOutput : Vector UInt8 32) :
    sourceCallerOrd (left.words,leftScalar,leftOutput) (right.words,rightScalar,rightOutput)
      leftScratch rightScratch = .eq ↔ left.words = right.words := by
  rw [original_caller_array_comparison_derives_the_original_field_numeric_order,Nat.compare_eq_eq]
  exact TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal left right
set_option pp.all true in
#check @sourceCallerByteKey
#print axioms sourceCallerByteKey
set_option pp.all true in
#check @source_caller_byte_key_has_exactly_32_bytes
#print axioms source_caller_byte_key_has_exactly_32_bytes
set_option pp.all true in
#check @qualified_sdk_serializer_is_the_exact_bounded_integer_encoding
#print axioms qualified_sdk_serializer_is_the_exact_bounded_integer_encoding
set_option pp.all true in
#check @reverse_integer_encoding_byte_is_the_exact_big_endian_quotient
#print axioms reverse_integer_encoding_byte_is_the_exact_big_endian_quotient
set_option pp.all true in
#check @original_caller_byte_key_is_exactly_the_qualified_reversed_sdk_encoding
#print axioms original_caller_byte_key_is_exactly_the_qualified_reversed_sdk_encoding
set_option pp.all true in
#check @sourceCallerOrd
#print axioms sourceCallerOrd
set_option pp.all true in
#check @original_caller_array_comparison_derives_the_original_field_numeric_order
#print axioms original_caller_array_comparison_derives_the_original_field_numeric_order
set_option pp.all true in
#check @canonical_original_caller_hash_inputs_equal_iff_original_raw_words_equal
#print axioms canonical_original_caller_hash_inputs_equal_iff_original_raw_words_equal
set_option pp.all true in
#check @canonical_original_caller_order_equality_agrees_with_original_raw_word_equality
#print axioms canonical_original_caller_order_equality_agrees_with_original_raw_word_equality
end ShielddSecurity.TransferBlstArmIdentity01
