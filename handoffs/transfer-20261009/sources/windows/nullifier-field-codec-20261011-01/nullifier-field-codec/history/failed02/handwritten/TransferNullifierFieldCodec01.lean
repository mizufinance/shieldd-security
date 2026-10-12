import ShielddSecurity.TransferScalarInputFamily01
import ShielddSecurity.TransferScalarChoiceMasks01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferNullifierFieldCodec01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferScalarInputFamily01 (sourceInputEval)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! The pinned Nullifier slice constructor first requires exactly 32 bytes,
then calls encoding::field, whose Fq alias is jubjub::Fq = bls12_381::Scalar.
This source-shaped success projection composes the qualified typed decoder,
R2 multiplication, canonical representation and serializer. All typed byte
lists are covered; accepted field meaning and round trips are derived.
The Rust alias/source association is recorded separately. Compiler, slice
conversion, Option/CtOption implementation, private constructor origins,
native callers and full Transfer correspondence remain open interfaces. -/

def sourceNullifierSliceDecode (bytes : List UInt8) : Option CanonicalScalar :=
  if width : bytes.length = 32 then
    sourceInputEval (.bytes ⟨bytes.toArray, by rw [List.size_toArray]; exact width⟩)
  else none

theorem typed_source_field_constructor_accepts_exact_canonical_domain (bytes : Vector UInt8 32) :
    (∃ scalar, sourceInputEval (.bytes bytes) = some scalar) ↔
      decodeLE bytes.toList < nullifierModulus := by
  rw [← TransferScalarChoiceBit01.source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus]
  by_cases yes : TransferScalarChoiceBit01.sourceCanonicalChoiceByte bytes = 1
  · constructor
    · intro _; exact yes
    · intro _; exact ⟨_, by rw [sourceInputEval, if_pos yes]⟩
  · constructor
    · rintro ⟨scalar, returned⟩
      rw [sourceInputEval, if_neg yes] at returned
      cases returned
    · intro accepted; exact False.elim (yes accepted)

theorem source_nullifier_slice_accepts_exact_width_and_canonical_integer (bytes : List UInt8) :
    (∃ scalar, sourceNullifierSliceDecode bytes = some scalar) ↔
      bytes.length = 32 ∧ decodeLE bytes < nullifierModulus := by
  by_cases width : bytes.length = 32
  · rw [sourceNullifierSliceDecode, dif_pos width,
      typed_source_field_constructor_accepts_exact_canonical_domain]
    simp only [Vector.toList, width, true_and]
  · rw [sourceNullifierSliceDecode, dif_neg width]
    simp only [reduceCtorEq, exists_const, width, false_and]

theorem returned_source_nullifier_has_exact_input_field_value_and_bytes
    (bytes : List UInt8) (scalar : CanonicalScalar)
    (returned : sourceNullifierSliceDecode bytes = some scalar) :
    montgomeryValue scalar.words = decodeLE bytes ∧
      serializerBytes scalar.words.toList = bytes := by
  have width := ((source_nullifier_slice_accepts_exact_width_and_canonical_integer bytes).mp
    ⟨scalar, returned⟩).1
  rw [sourceNullifierSliceDecode, dif_pos width] at returned
  have same := TransferScalarInputFamily01.returned_source_32_byte_family_constructor_reserializes_exact_original_bytes
    ⟨bytes.toArray, by rw [List.size_toArray]; exact width⟩ scalar returned
  simp only [Vector.toList] at same
  refine ⟨?_, same⟩
  rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
  exact congrArg decodeLE same

def sourceNullifierEncode (scalar : CanonicalScalar) : Vector UInt8 32 :=
  ⟨(serializerBytes scalar.words.toList).toArray, by
    rw [List.size_toArray]
    exact TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width
      scalar.words.toList Vector.length_toList⟩

theorem exact_source_nullifier_encoding_is_the_qualified_scalar_serializer (scalar : CanonicalScalar) :
    (sourceNullifierEncode scalar).toList = serializerBytes scalar.words.toList := by
  exact List.toList_toArray

theorem every_canonical_source_nullifier_encodes_to_its_mathematical_field (scalar : CanonicalScalar) :
    decodeLE (sourceNullifierEncode scalar).toList = montgomeryValue scalar.words := by
  rw [exact_source_nullifier_encoding_is_the_qualified_scalar_serializer]
  exact TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value scalar.words

theorem every_canonical_source_nullifier_encoding_decodes_to_the_original_field (scalar : CanonicalScalar) :
    sourceNullifierSliceDecode (sourceNullifierEncode scalar).toList = some scalar := by
  have encoded := exact_source_nullifier_encoding_is_the_qualified_scalar_serializer scalar
  have decoded := TransferScalarCanonicalDecoder01.canonical_raw_scalar_source_serialization_decodes_to_original_raw_vector
    scalar (sourceNullifierEncode scalar) encoded
  have projected := TransferScalarInputFamily01.source_32_byte_family_constructor_retains_exact_choice_success_projection
    (sourceNullifierEncode scalar)
  rw [decoded] at projected
  have original : sourceInputEval (.bytes (sourceNullifierEncode scalar)) = some scalar := by
    cases observed : sourceInputEval (.bytes (sourceNullifierEncode scalar)) with
    | none => rw [observed] at projected; cases projected
    | some restored =>
      rw [observed] at projected
      have words : restored.words = scalar.words := Option.some.inj projected
      have same := TransferScalarChoiceMasks01.canonical_scalar_objects_equal_of_exact_raw_word_equality restored scalar words
      rw [same]
  rw [sourceNullifierSliceDecode, dif_pos Vector.length_toList]
  simpa only [Vector.toArray_toList] using original

theorem returned_source_nullifier_decoding_is_injective_on_all_accepted_byte_lists
    (left right : List UInt8) (scalar : CanonicalScalar)
    (leftReturned : sourceNullifierSliceDecode left = some scalar)
    (rightReturned : sourceNullifierSliceDecode right = some scalar) : left = right := by
  exact (returned_source_nullifier_has_exact_input_field_value_and_bytes left scalar leftReturned).2.symm.trans
    (returned_source_nullifier_has_exact_input_field_value_and_bytes right scalar rightReturned).2

theorem source_nullifier_slice_rejects_every_incorrect_width
    (bytes : List UInt8) (wrongWidth : bytes.length ≠ 32) :
    sourceNullifierSliceDecode bytes = none := by
  rw [sourceNullifierSliceDecode, dif_neg wrongWidth]

set_option pp.all true in
#check @sourceNullifierSliceDecode
#print axioms sourceNullifierSliceDecode
set_option pp.all true in
#check @typed_source_field_constructor_accepts_exact_canonical_domain
#print axioms typed_source_field_constructor_accepts_exact_canonical_domain
set_option pp.all true in
#check @source_nullifier_slice_accepts_exact_width_and_canonical_integer
#print axioms source_nullifier_slice_accepts_exact_width_and_canonical_integer
set_option pp.all true in
#check @returned_source_nullifier_has_exact_input_field_value_and_bytes
#print axioms returned_source_nullifier_has_exact_input_field_value_and_bytes
set_option pp.all true in
#check @sourceNullifierEncode
#print axioms sourceNullifierEncode
set_option pp.all true in
#check @exact_source_nullifier_encoding_is_the_qualified_scalar_serializer
#print axioms exact_source_nullifier_encoding_is_the_qualified_scalar_serializer
set_option pp.all true in
#check @every_canonical_source_nullifier_encodes_to_its_mathematical_field
#print axioms every_canonical_source_nullifier_encodes_to_its_mathematical_field
set_option pp.all true in
#check @every_canonical_source_nullifier_encoding_decodes_to_the_original_field
#print axioms every_canonical_source_nullifier_encoding_decodes_to_the_original_field
set_option pp.all true in
#check @returned_source_nullifier_decoding_is_injective_on_all_accepted_byte_lists
#print axioms returned_source_nullifier_decoding_is_injective_on_all_accepted_byte_lists
set_option pp.all true in
#check @source_nullifier_slice_rejects_every_incorrect_width
#print axioms source_nullifier_slice_rejects_every_incorrect_width
end ShielddSecurity.TransferNullifierFieldCodec01
