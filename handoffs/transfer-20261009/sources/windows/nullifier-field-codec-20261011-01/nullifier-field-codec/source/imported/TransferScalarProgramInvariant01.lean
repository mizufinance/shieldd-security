import ShielddSecurity.TransferScalarCanonicalNeg01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarProgramInvariant01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarLittleEndianBytes01 (serializerBytes decodeLE)
open TransferScalarMontgomeryValue01 (montgomeryValue)
/-! A represented public Scalar operation family starts from arbitrary raw
four-word inputs converted by the actual modeled R2 multiplication, then
uses modeled add/sub/mul/neg/double. Every operation carries only its proved
output width and canonical bound; no caller operand invariant is supplied.
This family excludes square/pow/invert/from-wide/random and arbitrary private
construction. Rust caller/program and primitive/compiler coupling is OPEN. -/

inductive ScalarProgram where
  | raw (words : Vector UInt64 4)
  | add (left right : ScalarProgram)
  | sub (left right : ScalarProgram)
  | mul (left right : ScalarProgram)
  | neg (value : ScalarProgram)
  | double (value : ScalarProgram)

def certifyResult (words : List UInt64) (width : words.length = 4)
    (canonical : packWords words < nullifierModulus) : CanonicalScalar :=
  { words := ⟨words.toArray, by rw [List.size_toArray]; exact width⟩
    canonical := by
      change packWords words.toArray.toList < nullifierModulus
      rw [List.toList_toArray]
      exact canonical }

def sourceEval : ScalarProgram → CanonicalScalar
  | .raw words =>
    { words := TransferScalarR2Payload01.sourceDecoderPayload words
      canonical := (TransferScalarR2Payload01.decoder_payload_has_derived_canonical_raw_montgomery_value words).1 }
  | .add left right =>
    let l := sourceEval left
    let r := sourceEval right
    let contract := TransferScalarCanonicalAdd01.source_four_adc_and_modulus_sub_preserve_canonical_modular_sum l r
    certifyResult (TransferScalarCanonicalAdd01.sourceAddWords l.words r.words) contract.1 contract.2.1
  | .sub left right =>
    let l := sourceEval left
    let r := sourceEval right
    let width := TransferScalarCanonicalSub01.source_four_sbb_and_masked_adc_retain_four_output_limbs l.words r.words
    let contract := TransferScalarCanonicalSub01.canonical_operands_source_subtraction_has_exact_canonical_modular_value l r
    certifyResult (TransferScalarCanonicalSub01.sourceSubWords l.words r.words) width contract.1
  | .mul left right =>
    let l := sourceEval left
    let r := sourceEval right
    let contract := TransferScalarWideReduction01.canonical_right_operand_source_multiplication_has_derived_montgomery_contract
      l.words r.words r.canonical
    certifyResult (TransferScalarWideReduction01.sourceMulMontgomery l.words r.words) contract.1 contract.2.1
  | .neg value =>
    let v := sourceEval value
    let contract := TransferScalarCanonicalNeg01.source_four_sbb_and_nonzero_mask_derive_canonical_negation v
    certifyResult (TransferScalarCanonicalNeg01.sourceNegWords v.words) contract.1 contract.2.1
  | .double value =>
    let v := sourceEval value
    let contract := TransferScalarCanonicalAdd01.source_four_adc_and_modulus_sub_preserve_canonical_modular_sum v v
    certifyResult (TransferScalarCanonicalAdd01.sourceAddWords v.words v.words) contract.1 contract.2.1

theorem every_represented_source_program_derives_canonical_raw_fields_and_exact_serialized_key
    (program : ScalarProgram) :
    packWords (sourceEval program).words.toList < nullifierModulus ∧
      (serializerBytes (sourceEval program).words.toList).length = 32 ∧
      decodeLE (serializerBytes (sourceEval program).words.toList) < nullifierModulus ∧
      decodeLE (serializerBytes (sourceEval program).words.toList) = montgomeryValue (sourceEval program).words := by
  exact ⟨(sourceEval program).canonical,
    TransferCheckedWordAcceptedInput01.every_original_typed_field_has_exact_32_byte_canonical_serialized_key (sourceEval program)⟩

set_option pp.all true in
#check @ScalarProgram
#print axioms ScalarProgram
set_option pp.all true in
#check @certifyResult
#print axioms certifyResult
set_option pp.all true in
#check @sourceEval
#print axioms sourceEval
set_option pp.all true in
#check @every_represented_source_program_derives_canonical_raw_fields_and_exact_serialized_key
#print axioms every_represented_source_program_derives_canonical_raw_fields_and_exact_serialized_key
end ShielddSecurity.TransferScalarProgramInvariant01
