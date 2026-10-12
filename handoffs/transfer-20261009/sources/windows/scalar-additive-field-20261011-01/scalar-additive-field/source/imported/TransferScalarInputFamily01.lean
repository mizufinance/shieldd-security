import ShielddSecurity.TransferScalarWideByteInput01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarInputFamily01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarProgramInvariant01 (certifyResult)
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarCanonicalDecoder01 (byteDecoderPayload sourceDecodeOption)
open TransferScalarChoiceBit01 (sourceCanonicalChoiceByte)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Extend the represented source operation family with arbitrary64-byte
wide construction and canonical32-byte Choice success projection. Errors in
32-byte construction propagate through the symbolic program; every returned
field derives its invariant from exact proved constructor/operation outputs.
Square/pow/invert/random/private constructors and native program/ABI/library/
primitive/compiler binding remain separate; this is arithmetic model evidence. -/

inductive ScalarInputProgram where
  | raw (words : Vector UInt64 4)
  | wide (bytes : Vector UInt8 64)
  | bytes (value : Vector UInt8 32)
  | add (left right : ScalarInputProgram)
  | sub (left right : ScalarInputProgram)
  | mul (left right : ScalarInputProgram)
  | neg (value : ScalarInputProgram)
  | double (value : ScalarInputProgram)

def sourceInputEval : ScalarInputProgram → Option CanonicalScalar
  | .raw words => some (TransferScalarProgramInvariant01.sourceEval (.raw words))
  | .wide bytes => some ⟨TransferScalarWideByteInput01.sourceFromWideBytes bytes,
      (TransferScalarWideByteInput01.arbitrary_64_source_bytes_derive_canonical_field_and_exact_modular_key bytes).1⟩
  | .bytes bytes =>
      if sourceCanonicalChoiceByte bytes = 1 then
        some ⟨byteDecoderPayload bytes,
          (TransferScalarCanonicalDecoder01.source_byte_decoder_payload_has_derived_range_and_serialized_value bytes).1⟩
      else none
  | .add left right => do
      let l ← sourceInputEval left
      let r ← sourceInputEval right
      let contract := TransferScalarCanonicalAdd01.source_four_adc_and_modulus_sub_preserve_canonical_modular_sum l r
      return certifyResult (TransferScalarCanonicalAdd01.sourceAddWords l.words r.words) contract.1 contract.2.1
  | .sub left right => do
      let l ← sourceInputEval left
      let r ← sourceInputEval right
      let width := TransferScalarCanonicalSub01.source_four_sbb_and_masked_adc_retain_four_output_limbs l.words r.words
      let contract := TransferScalarCanonicalSub01.canonical_operands_source_subtraction_has_exact_canonical_modular_value l r
      return certifyResult (TransferScalarCanonicalSub01.sourceSubWords l.words r.words) width contract.1
  | .mul left right => do
      let l ← sourceInputEval left
      let r ← sourceInputEval right
      let contract := TransferScalarWideReduction01.canonical_right_operand_source_multiplication_has_derived_montgomery_contract
        l.words r.words r.canonical
      return certifyResult (TransferScalarWideReduction01.sourceMulMontgomery l.words r.words) contract.1 contract.2.1
  | .neg value => do
      let v ← sourceInputEval value
      let contract := TransferScalarCanonicalNeg01.source_four_sbb_and_nonzero_mask_derive_canonical_negation v
      return certifyResult (TransferScalarCanonicalNeg01.sourceNegWords v.words) contract.1 contract.2.1
  | .double value => do
      let v ← sourceInputEval value
      let contract := TransferScalarCanonicalAdd01.source_four_adc_and_modulus_sub_preserve_canonical_modular_sum v v
      return certifyResult (TransferScalarCanonicalAdd01.sourceAddWords v.words v.words) contract.1 contract.2.1

theorem source_32_byte_family_constructor_retains_exact_choice_success_projection (bytes : Vector UInt8 32) :
    (sourceInputEval (.bytes bytes)).map (fun scalar => scalar.words) = sourceDecodeOption bytes := by
  by_cases yes : sourceCanonicalChoiceByte bytes = 1
  · dsimp only [sourceInputEval, sourceDecodeOption]
    simp only [if_pos yes] <;> rfl
  · dsimp only [sourceInputEval, sourceDecodeOption]
    simp only [if_neg yes] <;> rfl

theorem returned_source_32_byte_family_constructor_reserializes_exact_original_bytes
    (bytes : Vector UInt8 32) (scalar : CanonicalScalar)
    (returned : sourceInputEval (.bytes bytes) = some scalar) :
    serializerBytes scalar.words.toList = bytes.toList := by
  have projected := congrArg (fun result : Option CanonicalScalar => result.map (fun value => value.words)) returned
  dsimp only at projected
  rw [source_32_byte_family_constructor_retains_exact_choice_success_projection] at projected
  change sourceDecodeOption bytes = some scalar.words at projected
  have canonical := (TransferScalarCanonicalDecoder01.source_decoder_success_projection_accepts_exactly_canonical_bytes bytes).mp
    ⟨scalar.words, projected⟩
  have roundtrip := TransferScalarCanonicalDecoder01.accepted_canonical_bytes_decode_and_reserialize_exactly bytes canonical
  have same : scalar.words = byteDecoderPayload bytes := Option.some.inj (projected.symm.trans roundtrip.1)
  rw [same]
  exact roundtrip.2

theorem every_returned_source_input_family_derives_canonical_fields_and_exact_serialized_key
    (program : ScalarInputProgram) :
    match sourceInputEval program with
    | none => True
    | some scalar => packWords scalar.words.toList < nullifierModulus ∧
        (serializerBytes scalar.words.toList).length = 32 ∧
        decodeLE (serializerBytes scalar.words.toList) < nullifierModulus ∧
        decodeLE (serializerBytes scalar.words.toList) = montgomeryValue scalar.words := by
  cases sourceInputEval program with
  | none => trivial
  | some scalar => exact ⟨scalar.canonical,
      TransferCheckedWordAcceptedInput01.every_original_typed_field_has_exact_32_byte_canonical_serialized_key scalar⟩

set_option pp.all true in
#check @ScalarInputProgram
#print axioms ScalarInputProgram
set_option pp.all true in
#check @sourceInputEval
#print axioms sourceInputEval
set_option pp.all true in
#check @source_32_byte_family_constructor_retains_exact_choice_success_projection
#print axioms source_32_byte_family_constructor_retains_exact_choice_success_projection
set_option pp.all true in
#check @returned_source_32_byte_family_constructor_reserializes_exact_original_bytes
#print axioms returned_source_32_byte_family_constructor_reserializes_exact_original_bytes
set_option pp.all true in
#check @every_returned_source_input_family_derives_canonical_fields_and_exact_serialized_key
#print axioms every_returned_source_input_family_derives_canonical_fields_and_exact_serialized_key
end ShielddSecurity.TransferScalarInputFamily01
