import ShielddSecurity.TransferBlstArmStage01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmPending01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBlstArmStage01 (sourceOriginalOrdContains sourceOriginalAdmitOpen)
open TransferNullifierBatchSource01 (BatchError uniqueLoop)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferScalarLittleEndianBytes01 (scalarKey)
attribute [local irreducible] scalarKey TransferBlstArmConstructor01.sourceFrFromLimbs

/-- The insert-result loop uses the exact original serialized comparator.
This is its extensional source contract; BTreeSet/imbl implementation and
ownership/async execution remain distinct correspondence obligations. -/
def sourceOriginalUniqueLoop : List CanonicalScalar → List CanonicalScalar → Bool
  | _, [] => true
  | seen, field :: rest =>
      if sourceOriginalOrdContains seen field then false
      else sourceOriginalUniqueLoop (field :: seen) rest

theorem original_comparator_contains_is_exact_original_key_contains
    (seen : List CanonicalScalar) (field : CanonicalScalar) :
    sourceOriginalOrdContains seen field =
      (seen.map (fun scalar => scalarKey scalar.words)).contains (scalarKey field.words) := by
  rw [TransferBlstArmStage01.original_caller_order_membership_is_exact_qualified_source_membership,
    TransferCanonicalSourceMembership01.source_ord_membership_is_exact_mapped_key_membership]

theorem original_insert_result_loop_is_exact_original_key_duplicate_loop
    (seen fields : List CanonicalScalar) :
    sourceOriginalUniqueLoop seen fields = uniqueLoop
      (seen.map (fun field => scalarKey field.words)) (fields.map (fun field => scalarKey field.words)) := by
  induction fields generalizing seen with
  | nil => rfl
  | cons field rest ih =>
      simp only [sourceOriginalUniqueLoop, uniqueLoop, List.map_cons,
        original_comparator_contains_is_exact_original_key_contains]
      split
      · rfl
      · exact ih (field :: seen)

def sourceOriginalAppend {Other : Type} (previous : Option (WordTaggedObject Other))
    (inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit) :
    Except Unit (Except BatchError (WordTaggedObject Other)) :=
  match TransferWordObjectRead01.checkedObject previous with
  | .error panic => .error panic
  | .ok pending =>
      match pending.getD (.opened [] []) with
      | .sealed _ => .ok (.error .sealed)
      | .opened ordered members =>
          match sourceOriginalAdmitOpen ordered members inputs checkDurable reader with
          | .error refusal => .ok (.error refusal)
          | .ok _ => (TransferWordObjectPut01.checkedPendingPut previous
              (.opened (ordered ++ inputs) (members ++ inputs))).map Except.ok

def sourceOriginalStage {Other : Type} (previous : Option (WordTaggedObject Other))
    (inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit) :
    Except Unit (Except BatchError (WordTaggedObject Other)) :=
  if sourceOriginalUniqueLoop [] inputs then sourceOriginalAppend previous inputs checkDurable reader
  else .ok (.error .duplicate)

theorem original_comparator_append_is_exact_original_field_append {Other : Type}
    (previous : Option (WordTaggedObject Other)) (inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit) :
    sourceOriginalAppend previous inputs checkDurable reader =
      TransferWordStageOrder01.appendAfterCheckedRead previous inputs checkDurable reader := by
  simp only [sourceOriginalAppend, TransferWordStageOrder01.appendAfterCheckedRead,
    TransferBlstArmStage01.original_caller_comparator_admission_is_the_qualified_original_field_admission]
  rfl

theorem original_comparator_whole_stage_is_exact_original_field_stage {Other : Type}
    (previous : Option (WordTaggedObject Other)) (inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit) :
    sourceOriginalStage previous inputs checkDurable reader =
      TransferWordStageOrder01.stageFields previous inputs checkDurable reader := by
  simp only [sourceOriginalStage, TransferWordStageOrder01.stageFields,
    original_insert_result_loop_is_exact_original_key_duplicate_loop, List.map_nil,
    original_comparator_append_is_exact_original_field_append]

theorem returned_original_comparator_stage_derives_all_checks_and_retains_entire_original_fields {Other : Type}
    (previous : Option (WordTaggedObject Other)) (inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit) (object : WordTaggedObject Other)
    (returned : sourceOriginalStage previous inputs checkDurable reader = .ok (.ok object)) :
    sourceOriginalUniqueLoop [] inputs = true ∧
      ∃ ordered members : List CanonicalScalar,
        ((previous = none ∧ ordered = [] ∧ members = []) ∨ previous = some (.inl (.opened ordered members))) ∧
        ordered.length + inputs.length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
        inputs.all (fun field => !sourceOriginalOrdContains members field) = true ∧
        (if checkDurable then reader inputs else .ok ()) = .ok () ∧
        object = .inl (.opened (ordered ++ inputs) (members ++ inputs)) := by
  rw [original_comparator_whole_stage_is_exact_original_field_stage] at returned
  have checks := TransferWordStageAdmission01.returned_whole_stage_derives_prior_typed_branch_all_checks_and_exact_original_field_append
    previous inputs checkDurable reader object returned
  simpa only [original_insert_result_loop_is_exact_original_key_duplicate_loop, List.map_nil,
    TransferBlstArmStage01.original_caller_order_membership_is_exact_qualified_source_membership] using checks

theorem original_duplicate_refusal_precedes_wrong_type_object_and_reader {Other : Type}
    (other : Other) (inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit)
    (duplicate : sourceOriginalUniqueLoop [] inputs = false) :
    sourceOriginalStage (some (.inr other)) inputs checkDurable reader = .ok (.error .duplicate) := by
  simp only [sourceOriginalStage, duplicate, Bool.false_eq_true, if_false]
set_option pp.all true in
#check @sourceOriginalUniqueLoop
#print axioms sourceOriginalUniqueLoop
set_option pp.all true in
#check @original_comparator_contains_is_exact_original_key_contains
#print axioms original_comparator_contains_is_exact_original_key_contains
set_option pp.all true in
#check @original_insert_result_loop_is_exact_original_key_duplicate_loop
#print axioms original_insert_result_loop_is_exact_original_key_duplicate_loop
set_option pp.all true in
#check @sourceOriginalAppend
#print axioms sourceOriginalAppend
set_option pp.all true in
#check @sourceOriginalStage
#print axioms sourceOriginalStage
set_option pp.all true in
#check @original_comparator_append_is_exact_original_field_append
#print axioms original_comparator_append_is_exact_original_field_append
set_option pp.all true in
#check @original_comparator_whole_stage_is_exact_original_field_stage
#print axioms original_comparator_whole_stage_is_exact_original_field_stage
set_option pp.all true in
#check @returned_original_comparator_stage_derives_all_checks_and_retains_entire_original_fields
#print axioms returned_original_comparator_stage_derives_all_checks_and_retains_entire_original_fields
set_option pp.all true in
#check @original_duplicate_refusal_precedes_wrong_type_object_and_reader
#print axioms original_duplicate_refusal_precedes_wrong_type_object_and_reader
end ShielddSecurity.TransferBlstArmPending01
