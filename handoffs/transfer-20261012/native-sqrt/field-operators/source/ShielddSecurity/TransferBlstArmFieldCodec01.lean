import ShielddSecurity.TransferBlstArmSdkBridge01
import ShielddSecurity.TransferBlstBeParser01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmFieldCodec01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarLittleEndianBytes01 (serializerBytes scalarKey)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferBlstArmNormalized01 (sourceArmFromMontVector)
open TransferBlstArmConstructor01 (sourceFrFromLimbs)
open TransferBlstBeParser01 (sourceReverseBytes sourceBEParseMemory64)
open TransferBlstByteCaller01 (sourceScalarLEBytes64 sourceLEParseMemory64)
attribute [local irreducible] Vector.ofFn serializerBytes scalarKey montgomeryValue
  sourceArmFromMontVector sourceFrFromLimbs sourceReverseBytes sourceBEParseMemory64
  sourceScalarLEBytes64 sourceLEParseMemory64 TransferBlstArmCaller01.sourceAsSlice
  TransferScalarBorrowWalk01.borrowWalk TransferScalarCanonicalNeg01.orWalk

/-! SDK field -> reverse bytes -> Commonware AllowZero read_cfg -> exact BE
parser -> scalar LE storage -> nonalias from_scalar LE parser -> left-rRR CIOS.
The SDK and Commonware private types/call paths remain distinct. The modeled
check retains four-limb underflow and nonzero/zero observations. Compiler/ISA,
ABI, distinct pointers, endian/limb selection, physical byte-zero observation
and codec Buf/read/error implementations remain separate native obligations.
No desired output, decoder success or canonical raw parsed payload is supplied. -/

def sourceSdkLEBytes (field : CanonicalScalar) : Vector UInt8 32 :=
  ⟨(serializerBytes field.words.toList).toArray, by
    rw [List.size_toArray]
    exact TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width _ Vector.length_toList⟩

theorem sdk_byte_vector_is_the_exact_original_sdk_serializer (field : CanonicalScalar) :
    (sourceSdkLEBytes field).toList = serializerBytes field.words.toList := by
  simp only [sourceSdkLEBytes,Vector.toList,List.toList_toArray]

theorem full_arm_from_mont_vector_has_the_original_input_numeric_value (field : CanonicalScalar) :
    packWords (sourceArmFromMontVector field.words).toList = montgomeryValue field.words := by
  rw [TransferBlstArmNormalized01.actual_full_from_mont_fixed_vector_is_the_actual_four_output_words]
  exact TransferBlstArmNormalized01.actual_full_from_mont_source_program_derives_the_original_montgomery_value field.words

theorem sdk_serializer_bytes_are_the_actual_limb_writer_of_derived_from_mont_words (field : CanonicalScalar) :
    sourceSdkLEBytes field = sourceScalarLEBytes64 (sourceArmFromMontVector field.words) := by
  apply Vector.toList_inj.mp
  rw [sdk_byte_vector_is_the_exact_original_sdk_serializer,
    TransferBlstByteRoundtrip01.actual_le_limb_writer_is_the_qualified_whole_integer_le_encoding,
    full_arm_from_mont_vector_has_the_original_input_numeric_value]
  exact TransferBlstArmIdentity01.qualified_sdk_serializer_is_the_exact_bounded_integer_encoding field.words

def sourceScalarFrCheckWords (raw : Vector UInt64 4) : Bool :=
  let underflow := (TransferScalarBorrowWalk01.borrowWalk false
    (raw.toList.zip TransferScalarFourRoundWrapper01.modulusWords)).2
  let nonzero := decide (TransferScalarCanonicalNeg01.orWalk 0 raw.toList ≠ 0)
  let zero := decide (TransferScalarCanonicalNeg01.orWalk 0 raw.toList = 0)
  (underflow && nonzero) || zero

theorem original_four_limb_check_underflow_is_exact_parsed_raw_modulus_range (raw : Vector UInt64 4) :
    (TransferScalarBorrowWalk01.borrowWalk false
      (raw.toList.zip TransferScalarFourRoundWrapper01.modulusWords)).2 = true ↔
      packWords raw.toList < nullifierModulus := by
  have underflow := TransferScalarBorrowWalk01.final_borrow_is_exact_input_underflow
    (raw.toList.zip TransferScalarFourRoundWrapper01.modulusWords)
  have leftWidth : raw.toList.length ≤ TransferScalarFourRoundWrapper01.modulusWords.length := by
    rw [Vector.length_toList,TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs]
  have rightWidth : TransferScalarFourRoundWrapper01.modulusWords.length ≤ raw.toList.length := by
    rw [Vector.length_toList,TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs]
  simpa only [List.map_fst_zip leftWidth,List.map_snd_zip rightWidth,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus] using underflow

theorem original_scalar_check_accepts_every_derived_canonical_raw_value_including_zero
    (raw : Vector UInt64 4) (canonical : packWords raw.toList < nullifierModulus) :
    sourceScalarFrCheckWords raw = true := by
  have borrow := (original_four_limb_check_underflow_is_exact_parsed_raw_modulus_range raw).mpr canonical
  rw [sourceScalarFrCheckWords,borrow,Bool.true_and]
  by_cases zero : TransferScalarCanonicalNeg01.orWalk 0 raw.toList = 0
  · simp only [zero,ne_self_iff_false,decide_false,decide_true,Bool.false_or]
  · have nonzero := decide_eq_true zero
    simp only [nonzero,Bool.true_or]

def sourceReadAllowZero (bytes : Vector UInt8 32) (parseScratch frScratch : Vector UInt64 4) : Option CanonicalScalar :=
  let parsed := sourceBEParseMemory64 bytes parseScratch
  let scalarMemory := sourceScalarLEBytes64 parsed
  let checkedWords := sourceLEParseMemory64 scalarMemory frScratch
  if sourceScalarFrCheckWords checkedWords then some (sourceFrFromLimbs checkedWords) else none

theorem reconstructing_original_from_mont_words_restores_the_entire_original_field (field : CanonicalScalar) :
    sourceFrFromLimbs (sourceArmFromMontVector field.words) = field := by
  apply TransferCanonicalSourceMembership01.canonical_source_key_is_injective_on_entire_typed_fields
  change scalarKey (sourceFrFromLimbs (sourceArmFromMontVector field.words)).words = scalarKey field.words
  rw [TransferBlstArmStage01.actual_constructor_input_projects_to_original_input_key_modulo_field,
    full_arm_from_mont_vector_has_the_original_input_numeric_value,
    TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
  have bounded : montgomeryValue field.words < nullifierModulus := by
    rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
    exact TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical field.words
  exact Nat.mod_eq_of_lt bounded

theorem original_sdk_field_to_commonware_allowzero_call_returns_the_entire_original_field
    (field : CanonicalScalar) (parseScratch frScratch : Vector UInt64 4) :
    sourceReadAllowZero (sourceReverseBytes (sourceSdkLEBytes field)) parseScratch frScratch = some field := by
  have canonical : packWords (sourceArmFromMontVector field.words).toList < nullifierModulus := by
    rw [full_arm_from_mont_vector_has_the_original_input_numeric_value,
      ← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
    exact TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical field.words
  rw [sourceReadAllowZero,sdk_serializer_bytes_are_the_actual_limb_writer_of_derived_from_mont_words,
    TransferBlstBeParser01.actual_be_parser_of_actual_reversed_le_writer_recovers_every_original_limb,
    TransferBlstByteRoundtrip01.actual_le_writer_parser_roundtrip_is_the_original_four_limb_vector,
    original_scalar_check_accepts_every_derived_canonical_raw_value_including_zero _ canonical]
  simp only [if_true,reconstructing_original_from_mont_words_restores_the_entire_original_field]
theorem actual_reverse_byte_index_map_is_the_original_vector_reverse (bytes : Vector UInt8 32) :
    sourceReverseBytes bytes = bytes.reverse := by
  apply Vector.ext
  intro index inside
  simp only [sourceReverseBytes,Vector.getElem_ofFn,Vector.getElem_reverse]

theorem actual_reverse_byte_index_map_reverses_the_entire_original_byte_list (bytes : Vector UInt8 32) :
    (sourceReverseBytes bytes).toList = bytes.toList.reverse := by
  rw [actual_reverse_byte_index_map_is_the_original_vector_reverse,Vector.toList_reverse]

def sourceCommonwareToSdkWords (field : CanonicalScalar) (scalarPrior outputPrior : Vector UInt8 32)
    (scratch : Vector UInt64 4) : Option (Vector UInt64 4) :=
  TransferScalarCanonicalDecoder01.sourceDecodeOption
    (sourceReverseBytes (TransferBlstArmCaller01.sourceAsSlice (field.words,scalarPrior,outputPrior) scratch).2.2)

theorem original_commonware_native_field_call_returns_the_entire_original_sdk_word_vector
    (field : CanonicalScalar) (scalarPrior outputPrior : Vector UInt8 32) (scratch : Vector UInt64 4) :
    sourceCommonwareToSdkWords field scalarPrior outputPrior scratch = some field.words := by
  have caller := TransferBlstArmIdentity01.original_caller_byte_key_is_exactly_the_qualified_reversed_sdk_encoding
    (field.words,scalarPrior,outputPrior) scratch
  have encoded : (TransferBlstArmCaller01.sourceAsSlice (field.words,scalarPrior,outputPrior) scratch).2.2.toList =
      (serializerBytes field.words.toList).reverse := by
    simpa only [TransferBlstArmIdentity01.sourceCallerByteKey] using caller
  have bytes : (sourceReverseBytes
      (TransferBlstArmCaller01.sourceAsSlice (field.words,scalarPrior,outputPrior) scratch).2.2).toList =
      serializerBytes field.words.toList := by
    rw [actual_reverse_byte_index_map_reverses_the_entire_original_byte_list,encoded,List.reverse_reverse]
  exact TransferScalarCanonicalDecoder01.canonical_raw_scalar_source_serialization_decodes_to_original_raw_vector field _ bytes
set_option pp.all true in
#check @sourceSdkLEBytes
#print axioms sourceSdkLEBytes
set_option pp.all true in
#check @sdk_byte_vector_is_the_exact_original_sdk_serializer
#print axioms sdk_byte_vector_is_the_exact_original_sdk_serializer
set_option pp.all true in
#check @full_arm_from_mont_vector_has_the_original_input_numeric_value
#print axioms full_arm_from_mont_vector_has_the_original_input_numeric_value
set_option pp.all true in
#check @sdk_serializer_bytes_are_the_actual_limb_writer_of_derived_from_mont_words
#print axioms sdk_serializer_bytes_are_the_actual_limb_writer_of_derived_from_mont_words
set_option pp.all true in
#check @sourceScalarFrCheckWords
#print axioms sourceScalarFrCheckWords
set_option pp.all true in
#check @original_four_limb_check_underflow_is_exact_parsed_raw_modulus_range
#print axioms original_four_limb_check_underflow_is_exact_parsed_raw_modulus_range
set_option pp.all true in
#check @original_scalar_check_accepts_every_derived_canonical_raw_value_including_zero
#print axioms original_scalar_check_accepts_every_derived_canonical_raw_value_including_zero
set_option pp.all true in
#check @sourceReadAllowZero
#print axioms sourceReadAllowZero
set_option pp.all true in
#check @reconstructing_original_from_mont_words_restores_the_entire_original_field
#print axioms reconstructing_original_from_mont_words_restores_the_entire_original_field
set_option pp.all true in
#check @original_sdk_field_to_commonware_allowzero_call_returns_the_entire_original_field
#print axioms original_sdk_field_to_commonware_allowzero_call_returns_the_entire_original_field
set_option pp.all true in
#check @actual_reverse_byte_index_map_is_the_original_vector_reverse
#print axioms actual_reverse_byte_index_map_is_the_original_vector_reverse
set_option pp.all true in
#check @actual_reverse_byte_index_map_reverses_the_entire_original_byte_list
#print axioms actual_reverse_byte_index_map_reverses_the_entire_original_byte_list
set_option pp.all true in
#check @sourceCommonwareToSdkWords
#print axioms sourceCommonwareToSdkWords
set_option pp.all true in
#check @original_commonware_native_field_call_returns_the_entire_original_sdk_word_vector
#print axioms original_commonware_native_field_call_returns_the_entire_original_sdk_word_vector
end ShielddSecurity.TransferBlstArmFieldCodec01
