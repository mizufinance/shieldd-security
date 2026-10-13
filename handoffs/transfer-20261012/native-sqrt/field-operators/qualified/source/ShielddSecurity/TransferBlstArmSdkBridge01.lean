import ShielddSecurity.TransferBlstArmStage01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmSdkBridge01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBlstArmConstructor01 (sourceFrFromLimbs)
open TransferScalarProgramInvariant01 (sourceEval)
open TransferScalarLittleEndianBytes01 (scalarKey serializerBytes)
attribute [local irreducible] sourceFrFromLimbs scalarKey
  TransferScalarR2Payload01.sourceDecoderPayload sourceEval

/-! Exact SDK from_raw and BLST from_uint64 source-model word correspondence,
for every original four-limb input. SDK schoolbook/wide Montgomery multiplication
and ARM CIOS each derive their result; no matching output or canonical-input
premise is provided. SDK SCT Nullifier and Commonware Scalar remain distinct
native call paths. This bridge does not prove native compiler/ISA/ABI execution
or an exhaustive actual private producer census. -/

theorem original_sdk_raw_constructor_and_arm_cios_constructor_return_the_same_entire_field
    (raw : Vector UInt64 4) : sourceFrFromLimbs raw = sourceEval (.raw raw) := by
  apply TransferCanonicalSourceMembership01.canonical_source_key_is_injective_on_entire_typed_fields
  change scalarKey (sourceFrFromLimbs raw).words = scalarKey (sourceEval (.raw raw)).words
  rw [TransferBlstArmStage01.actual_constructor_input_projects_to_original_input_key_modulo_field]
  have sdk := TransferScalarR2Payload01.actual_modeled_decoder_payload_serializer_returns_raw_modulus_value raw
  simpa only [sourceEval] using sdk.symm

theorem original_sdk_raw_constructor_and_arm_cios_constructor_return_the_same_four_private_words
    (raw : Vector UInt64 4) :
    (sourceFrFromLimbs raw).words = TransferScalarR2Payload01.sourceDecoderPayload raw := by
  simpa only [sourceEval] using congrArg CanonicalScalar.words
    (original_sdk_raw_constructor_and_arm_cios_constructor_return_the_same_entire_field raw)

theorem original_sdk_raw_field_words_reach_the_commonware_caller_as_original_input_field_bytes
    (raw : Vector UInt64 4) (scalarPrior outputPrior : Vector UInt8 32)
    (scratch : Vector UInt64 4) (index : Fin 32) :
    (TransferBlstArmCaller01.sourceAsSlice
      ((sourceEval (.raw raw)).words,scalarPrior,outputPrior) scratch).2.2[index.val] =
      TransferCommonwareMapBytes01.canonicalBEByte
        (TransferScalarWordPrimitives01.packWords raw.toList : ZMod TransferBoundedNativeCodec01.nullifierModulus) index := by
  rw [← original_sdk_raw_constructor_and_arm_cios_constructor_return_the_same_entire_field]
  exact TransferBlstArmConstructor01.original_locked_constructor_and_original_as_slice_caller_derive_every_original_input_field_byte
    raw scalarPrior outputPrior scratch index

theorem original_sdk_nullifier_order_observation_and_commonware_caller_observation_are_equal
    (left right : CanonicalScalar) :
    TransferScalarReversedByteOrder01.compareHighFirst (serializerBytes left.words.toList).reverse
      (serializerBytes right.words.toList).reverse =
      TransferBlstArmIdentity01.sourceCallerOrd
        (TransferBlstArmStage01.sourceScalarCallerMemory left)
        (TransferBlstArmStage01.sourceScalarCallerMemory right)
        (Vector.replicate 4 0) (Vector.replicate 4 0) := by
  rw [TransferScalarReversedByteOrder01.source_reversed_32_byte_comparison_is_exact_mathematical_montgomery_order,
    TransferBlstArmIdentity01.original_caller_array_comparison_derives_the_original_field_numeric_order]
  rfl

theorem original_sdk_and_arm_constructor_batches_retain_the_same_entire_ordered_fields
    (raws : List (Vector UInt64 4)) :
    raws.map sourceFrFromLimbs = raws.map (fun raw => sourceEval (.raw raw)) := by
  apply congrArg (fun function : Vector UInt64 4 → CanonicalScalar => raws.map function)
  funext raw
  exact original_sdk_raw_constructor_and_arm_cios_constructor_return_the_same_entire_field raw
set_option pp.all true in
#check @original_sdk_raw_constructor_and_arm_cios_constructor_return_the_same_entire_field
#print axioms original_sdk_raw_constructor_and_arm_cios_constructor_return_the_same_entire_field
set_option pp.all true in
#check @original_sdk_raw_constructor_and_arm_cios_constructor_return_the_same_four_private_words
#print axioms original_sdk_raw_constructor_and_arm_cios_constructor_return_the_same_four_private_words
set_option pp.all true in
#check @original_sdk_raw_field_words_reach_the_commonware_caller_as_original_input_field_bytes
#print axioms original_sdk_raw_field_words_reach_the_commonware_caller_as_original_input_field_bytes
set_option pp.all true in
#check @original_sdk_nullifier_order_observation_and_commonware_caller_observation_are_equal
#print axioms original_sdk_nullifier_order_observation_and_commonware_caller_observation_are_equal
set_option pp.all true in
#check @original_sdk_and_arm_constructor_batches_retain_the_same_entire_ordered_fields
#print axioms original_sdk_and_arm_constructor_batches_retain_the_same_entire_ordered_fields
end ShielddSecurity.TransferBlstArmSdkBridge01
