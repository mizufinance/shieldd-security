import ShielddSecurity.TransferScalarPublicConstants01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarExtendedFamily01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarInputFamily01 (ScalarInputProgram sourceInputEval)
open TransferScalarPublicConstants01 (PublicConstant sourceConstant)
open TransferScalarPowInvariant01 (sourceZero sourceOne sourceCanonicalMul sourceCanonicalSquare sourcePow sourcePowVartime)
open TransferScalarProgramInvariant01 (certifyResult)
open TransferScalarInvertChain01 (sourceInvert)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarLittleEndianBytes01 (serializerBytes decodeLE)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Extend the source-derived returned Scalar operation family with public
constants, ZERO/ONE, u64/raw conversion, arbitrary random64-byte input,
optimized square, both pow loops, exact modeled inversion and Boolean
selection. Constructor failures propagate. All operand bounds are derived
from evaluated program results, never caller hypotheses. Native API origin,
RNG/Choice/conditional selection/compiler/caller coupling remains separate. -/

inductive ScalarExtendedProgram where
  | input (program : ScalarInputProgram)
  | constant (value : PublicConstant)
  | zero
  | one
  | fromU64 (value : UInt64)
  | randomBytes (bytes : Vector UInt8 64)
  | add (left right : ScalarExtendedProgram)
  | sub (left right : ScalarExtendedProgram)
  | mul (left right : ScalarExtendedProgram)
  | neg (value : ScalarExtendedProgram)
  | double (value : ScalarExtendedProgram)
  | square (value : ScalarExtendedProgram)
  | pow (value : ScalarExtendedProgram) (exponent : Vector UInt64 4)
  | powVartime (value : ScalarExtendedProgram) (exponent : Vector UInt64 4)
  | invert (value : ScalarExtendedProgram)
  | select (choice : Bool) (first second : ScalarExtendedProgram)

def sourceExtendedEval : ScalarExtendedProgram → Option CanonicalScalar
  | .input program => sourceInputEval program
  | .constant value => some (sourceConstant value)
  | .zero => some sourceZero
  | .one => some sourceOne
  | .fromU64 value => sourceInputEval (.raw #v[value, 0, 0, 0])
  | .randomBytes bytes => sourceInputEval (.wide bytes)
  | .add left right => do
    let l ← sourceExtendedEval left
    let r ← sourceExtendedEval right
    let contract := TransferScalarCanonicalAdd01.source_four_adc_and_modulus_sub_preserve_canonical_modular_sum l r
    return certifyResult (TransferScalarCanonicalAdd01.sourceAddWords l.words r.words) contract.1 contract.2.1
  | .sub left right => do
    let l ← sourceExtendedEval left
    let r ← sourceExtendedEval right
    let width := TransferScalarCanonicalSub01.source_four_sbb_and_masked_adc_retain_four_output_limbs l.words r.words
    let contract := TransferScalarCanonicalSub01.canonical_operands_source_subtraction_has_exact_canonical_modular_value l r
    return certifyResult (TransferScalarCanonicalSub01.sourceSubWords l.words r.words) width contract.1
  | .mul left right => do
    let l ← sourceExtendedEval left
    let r ← sourceExtendedEval right
    return sourceCanonicalMul l r
  | .neg value => do
    let v ← sourceExtendedEval value
    let contract := TransferScalarCanonicalNeg01.source_four_sbb_and_nonzero_mask_derive_canonical_negation v
    return certifyResult (TransferScalarCanonicalNeg01.sourceNegWords v.words) contract.1 contract.2.1
  | .double value => do
    let v ← sourceExtendedEval value
    let contract := TransferScalarCanonicalAdd01.source_four_adc_and_modulus_sub_preserve_canonical_modular_sum v v
    return certifyResult (TransferScalarCanonicalAdd01.sourceAddWords v.words v.words) contract.1 contract.2.1
  | .square value => do
    let v ← sourceExtendedEval value
    return sourceCanonicalSquare v
  | .pow value exponent => do
    let v ← sourceExtendedEval value
    return sourcePow v exponent
  | .powVartime value exponent => do
    let v ← sourceExtendedEval value
    return sourcePowVartime v exponent
  | .invert value => do
    let v ← sourceExtendedEval value
    sourceInvert v
  | .select choice first second => do
    let a ← sourceExtendedEval first
    let b ← sourceExtendedEval second
    return if choice then b else a

theorem every_returned_extended_source_program_derives_canonical_raw_fields_and_exact_key
    (program : ScalarExtendedProgram) :
    match sourceExtendedEval program with
    | none => True
    | some scalar => packWords scalar.words.toList < nullifierModulus ∧
        (serializerBytes scalar.words.toList).length = 32 ∧
        decodeLE (serializerBytes scalar.words.toList) < nullifierModulus ∧
        decodeLE (serializerBytes scalar.words.toList) = montgomeryValue scalar.words := by
  cases sourceExtendedEval program with
  | none => trivial
  | some scalar => exact ⟨scalar.canonical,
      TransferCheckedWordAcceptedInput01.every_original_typed_field_has_exact_32_byte_canonical_serialized_key scalar⟩

theorem extended_source_invert_refuses_constructor_failure_or_exact_zero_payload
    (program : ScalarExtendedProgram) :
    sourceExtendedEval (.invert program) = none ↔
      match sourceExtendedEval program with
      | none => True
      | some scalar => scalar.words = sourceZero.words := by
  change (sourceExtendedEval program).bind sourceInvert = none ↔
    match sourceExtendedEval program with
    | none => True
    | some scalar => scalar.words = sourceZero.words
  cases sourceExtendedEval program with
  | none => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | some scalar =>
    change sourceInvert scalar = none ↔ scalar.words = sourceZero.words
    exact TransferScalarInvertChain01.exact_source_invert_zero_refusal_is_derived scalar

set_option pp.all true in
#check @ScalarExtendedProgram
#print axioms ScalarExtendedProgram
set_option pp.all true in
#check @sourceExtendedEval
#print axioms sourceExtendedEval
set_option pp.all true in
#check @every_returned_extended_source_program_derives_canonical_raw_fields_and_exact_key
#print axioms every_returned_extended_source_program_derives_canonical_raw_fields_and_exact_key
set_option pp.all true in
#check @extended_source_invert_refuses_constructor_failure_or_exact_zero_payload
#print axioms extended_source_invert_refuses_constructor_failure_or_exact_zero_payload
end ShielddSecurity.TransferScalarExtendedFamily01
