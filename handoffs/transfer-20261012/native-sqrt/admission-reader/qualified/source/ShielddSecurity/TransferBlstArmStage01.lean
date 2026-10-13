import ShielddSecurity.TransferBlstArmConstructor01
import ShielddSecurity.TransferBlstArmIdentity01
import ShielddSecurity.TransferWordStageAdmission01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmStage01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBlstArmCaller01 (CallerMemory)
open TransferBlstArmIdentity01 (sourceCallerOrd)
open TransferNullifierBatchSource01 (BatchError)
open TransferWordObjectCodec01 (WordTaggedObject)
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
  TransferBlstArmCaller01.sourceAsSlice TransferBlstArmIdentity01.sourceCallerByteKey
  TransferBlstArmConstructor01.sourceFrFromLimbs

def sourceScalarCallerMemory (scalar : CanonicalScalar) : CallerMemory :=
  (scalar.words,Vector.replicate 32 0,Vector.replicate 32 0)

/-- Extensional membership using the original caller's serialized Ord equality.
Concrete collection/iterator, Any/Clone/async/ABI/compiler correspondence remains
separate; the comparator and constructor values are derived here. -/
def sourceOriginalOrdContains (fields : List CanonicalScalar) (scalar : CanonicalScalar) : Bool :=
  fields.any (fun candidate => decide (sourceCallerOrd (sourceScalarCallerMemory candidate)
    (sourceScalarCallerMemory scalar) (Vector.replicate 4 0) (Vector.replicate 4 0) = .eq))

theorem original_caller_order_membership_is_exact_qualified_source_membership
    (fields : List CanonicalScalar) (scalar : CanonicalScalar) :
    sourceOriginalOrdContains fields scalar = TransferCanonicalSourceMembership01.sourceOrdContains fields scalar := by
  unfold sourceOriginalOrdContains TransferCanonicalSourceMembership01.sourceOrdContains
  apply congrArg (fun predicate : CanonicalScalar → Bool => fields.any predicate)
  funext candidate
  rw [TransferBlstArmIdentity01.original_caller_array_comparison_derives_the_original_field_numeric_order,
    TransferScalarReversedByteOrder01.source_reversed_32_byte_comparison_is_exact_mathematical_montgomery_order]
  rfl

def sourceOriginalAdmitOpen (ordered members inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit) : Except BatchError Unit :=
  if TransferPendingSaturatingCapacity01.sourceSaturatingLengthAdd 64 ordered.length inputs.length ≤
      TransferNullifierConsensusLimits01.blockCapacity then
    if inputs.all (fun scalar => !sourceOriginalOrdContains members scalar) then
      if checkDurable then reader inputs else .ok ()
    else .error .pending
  else .error .capacity

theorem original_caller_comparator_admission_is_the_qualified_original_field_admission
    (ordered members inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit) :
    sourceOriginalAdmitOpen ordered members inputs checkDurable reader =
      TransferWordStageOrder01.admitOpen ordered members inputs checkDurable reader := by
  simp only [sourceOriginalAdmitOpen,TransferWordStageOrder01.admitOpen,
    original_caller_order_membership_is_exact_qualified_source_membership]

theorem returned_original_comparator_admission_derives_capacity_freshness_and_required_reader_success
    (ordered members inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit)
    (returned : sourceOriginalAdmitOpen ordered members inputs checkDurable reader = .ok ()) :
    ordered.length+inputs.length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
      inputs.all (fun scalar => !sourceOriginalOrdContains members scalar) = true ∧
      (if checkDurable then reader inputs else .ok ()) = .ok () := by
  rw [original_caller_comparator_admission_is_the_qualified_original_field_admission] at returned
  have result := TransferWordStageAdmission01.returned_admission_derives_natural_capacity_freshness_and_required_reader_success
    ordered members inputs checkDurable reader returned
  simpa only [original_caller_order_membership_is_exact_qualified_source_membership] using result

theorem actual_constructor_input_projects_to_original_input_key_modulo_field (raw : Vector UInt64 4) :
    TransferScalarLittleEndianBytes01.scalarKey (TransferBlstArmConstructor01.sourceFrFromLimbs raw).words =
      TransferScalarWordPrimitives01.packWords raw.toList%TransferBoundedNativeCodec01.nullifierModulus := by
  rw [TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
  exact TransferBlstArmConstructor01.original_locked_constructor_derives_the_original_four_limb_integer_field_value raw

theorem original_constructor_batch_entire_word_fields_are_unique_exactly_when_original_input_keys_are_unique
    (raw : List (Vector UInt64 4)) :
    (raw.map TransferBlstArmConstructor01.sourceFrFromLimbs).Nodup ↔
      (raw.map (fun words => TransferScalarWordPrimitives01.packWords words.toList%
        TransferBoundedNativeCodec01.nullifierModulus)).Nodup := by
  rw [← TransferCanonicalSourceMembership01.mapped_source_key_uniqueness_iff_original_typed_field_uniqueness,
    List.map_map]
  simp only [Function.comp_def,actual_constructor_input_projects_to_original_input_key_modulo_field]

theorem original_comparator_refuses_pending_collisions_before_the_durable_reader
    (ordered members inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit)
    (capacity : TransferPendingSaturatingCapacity01.sourceSaturatingLengthAdd 64 ordered.length inputs.length ≤
      TransferNullifierConsensusLimits01.blockCapacity)
    (collision : inputs.all (fun scalar => !sourceOriginalOrdContains members scalar)=false) :
    sourceOriginalAdmitOpen ordered members inputs checkDurable reader = .error .pending := by
  simp only [sourceOriginalAdmitOpen,if_pos capacity,collision,Bool.false_eq_true,if_false]
set_option pp.all true in
#check @sourceScalarCallerMemory
#print axioms sourceScalarCallerMemory
set_option pp.all true in
#check @sourceOriginalOrdContains
#print axioms sourceOriginalOrdContains
set_option pp.all true in
#check @original_caller_order_membership_is_exact_qualified_source_membership
#print axioms original_caller_order_membership_is_exact_qualified_source_membership
set_option pp.all true in
#check @sourceOriginalAdmitOpen
#print axioms sourceOriginalAdmitOpen
set_option pp.all true in
#check @original_caller_comparator_admission_is_the_qualified_original_field_admission
#print axioms original_caller_comparator_admission_is_the_qualified_original_field_admission
set_option pp.all true in
#check @returned_original_comparator_admission_derives_capacity_freshness_and_required_reader_success
#print axioms returned_original_comparator_admission_derives_capacity_freshness_and_required_reader_success
set_option pp.all true in
#check @actual_constructor_input_projects_to_original_input_key_modulo_field
#print axioms actual_constructor_input_projects_to_original_input_key_modulo_field
set_option pp.all true in
#check @original_constructor_batch_entire_word_fields_are_unique_exactly_when_original_input_keys_are_unique
#print axioms original_constructor_batch_entire_word_fields_are_unique_exactly_when_original_input_keys_are_unique
set_option pp.all true in
#check @original_comparator_refuses_pending_collisions_before_the_durable_reader
#print axioms original_comparator_refuses_pending_collisions_before_the_durable_reader
end ShielddSecurity.TransferBlstArmStage01
