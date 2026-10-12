import ShielddSecurity.TransferWordStageOrder01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWordStageAdmission01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferNullifierBatchSource01 (BatchError uniqueLoop)
open TransferCanonicalSourceMembership01 (sourceOrdContains)
open TransferWordStageOrder01 (admitOpen appendAfterCheckedRead stageFields)
open TransferWordObjectRead01 (checkedObject)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferPendingSaturatingCapacity01 (sourceSaturatingLengthAdd)
open TransferScalarLittleEndianBytes01 (scalarKey)
/-! Admission checks precede the optional durable-reader interface and guarded
write. Returned staging success derives the natural capacity, pending freshness,
required reader success, actual typed previous/default branch and exact original
field append. No admitted result or desired next object is supplied to that
whole-stage theorem. Native collection/reader/usize/Scalar/Any/compiler/delta/
async correspondence remains OPEN; source-model credit only. -/

theorem capacity_refusal_precedes_membership_and_reader
    (ordered members inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit)
    (over : ¬ sourceSaturatingLengthAdd 64 ordered.length inputs.length ≤ blockCapacity) :
    admitOpen ordered members inputs checkDurable reader = .error .capacity := by
  simp only [admitOpen, if_neg over]

theorem pending_collision_refusal_precedes_reader
    (ordered members inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit)
    (capacity : sourceSaturatingLengthAdd 64 ordered.length inputs.length ≤ blockCapacity)
    (collision : inputs.all (fun scalar => !sourceOrdContains members scalar) = false) :
    admitOpen ordered members inputs checkDurable reader = .error .pending := by
  simp only [admitOpen, if_pos capacity, collision, Bool.false_eq_true, if_false]

theorem disabled_durable_check_skips_reader_after_capacity_and_freshness
    (ordered members inputs : List CanonicalScalar) (reader : List CanonicalScalar → Except BatchError Unit)
    (capacity : sourceSaturatingLengthAdd 64 ordered.length inputs.length ≤ blockCapacity)
    (fresh : inputs.all (fun scalar => !sourceOrdContains members scalar) = true) :
    admitOpen ordered members inputs false reader = .ok () := by
  simp only [admitOpen, if_pos capacity, fresh, if_true, Bool.false_eq_true, if_false]

theorem enabled_durable_check_returns_exact_reader_result_after_prior_checks
    (ordered members inputs : List CanonicalScalar) (reader : List CanonicalScalar → Except BatchError Unit)
    (capacity : sourceSaturatingLengthAdd 64 ordered.length inputs.length ≤ blockCapacity)
    (fresh : inputs.all (fun scalar => !sourceOrdContains members scalar) = true) :
    admitOpen ordered members inputs true reader = reader inputs := by
  simp only [admitOpen, if_pos capacity, fresh, if_true]

theorem returned_admission_derives_natural_capacity_freshness_and_required_reader_success
    (ordered members inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit)
    (success : admitOpen ordered members inputs checkDurable reader = .ok ()) :
    ordered.length + inputs.length ≤ blockCapacity ∧
      inputs.all (fun scalar => !sourceOrdContains members scalar) = true ∧
      (if checkDurable then reader inputs else .ok ()) = .ok () := by
  unfold admitOpen at success
  split at success
  next capacity =>
    split at success
    next fresh =>
      exact ⟨(TransferPendingSaturatingCapacity01.source_32_and_64_bit_pending_gates_accept_exactly_the_consensus_sum_bound
        ordered.length inputs.length).2.mp capacity, fresh, success⟩
    next collision => cases success
  next over => cases success

theorem returned_whole_stage_derives_prior_typed_branch_all_checks_and_exact_original_field_append {Other : Type}
    (previous : Option (WordTaggedObject Other)) (inputs : List CanonicalScalar) (checkDurable : Bool)
    (reader : List CanonicalScalar → Except BatchError Unit) (object : WordTaggedObject Other)
    (success : stageFields previous inputs checkDurable reader = .ok (.ok object)) :
    uniqueLoop [] (inputs.map (fun scalar => scalarKey scalar.words)) = true ∧
      ∃ ordered members : List CanonicalScalar,
        ((previous = none ∧ ordered = [] ∧ members = []) ∨ previous = some (.inl (.opened ordered members))) ∧
        ordered.length + inputs.length ≤ blockCapacity ∧
        inputs.all (fun scalar => !sourceOrdContains members scalar) = true ∧
        (if checkDurable then reader inputs else .ok ()) = .ok () ∧
        object = .inl (.opened (ordered ++ inputs) (members ++ inputs)) := by
  unfold stageFields at success
  split at success
  next unique =>
    refine ⟨unique, ?_⟩
    cases previous with
    | none =>
      simp only [appendAfterCheckedRead, checkedObject, Option.getD_none] at success
      cases admitted : admitOpen [] [] inputs checkDurable reader with
      | error refusal => simp only [admitted] at success; cases success
      | ok unitValue =>
        cases unitValue
        rw [admitted] at success
        have written : (.inl (.opened ([] ++ inputs) ([] ++ inputs)) : WordTaggedObject Other) = object :=
          Except.ok.inj (Except.ok.inj success)
        obtain ⟨capacity, fresh, durable⟩ := returned_admission_derives_natural_capacity_freshness_and_required_reader_success
          [] [] inputs checkDurable reader admitted
        exact ⟨[], [], Or.inl ⟨rfl, rfl, rfl⟩, capacity, fresh, durable, written.symm⟩
    | some present =>
      cases present with
      | inr other => simp only [appendAfterCheckedRead, checkedObject] at success; cases success
      | inl pending =>
        cases pending with
        | sealed ordered =>
          simp only [appendAfterCheckedRead, checkedObject, Option.getD_some] at success
          cases success
        | opened ordered members =>
          simp only [appendAfterCheckedRead, checkedObject, Option.getD_some] at success
          cases admitted : admitOpen ordered members inputs checkDurable reader with
          | error refusal => simp only [admitted] at success; cases success
          | ok unitValue =>
            cases unitValue
            rw [admitted] at success
            have written : (.inl (.opened (ordered ++ inputs) (members ++ inputs)) : WordTaggedObject Other) = object :=
              Except.ok.inj (Except.ok.inj success)
            obtain ⟨capacity, fresh, durable⟩ := returned_admission_derives_natural_capacity_freshness_and_required_reader_success
              ordered members inputs checkDurable reader admitted
            exact ⟨ordered, members, Or.inr rfl, capacity, fresh, durable, written.symm⟩
  next duplicate => cases success

set_option pp.all true in
#check @capacity_refusal_precedes_membership_and_reader
#print axioms capacity_refusal_precedes_membership_and_reader
set_option pp.all true in
#check @pending_collision_refusal_precedes_reader
#print axioms pending_collision_refusal_precedes_reader
set_option pp.all true in
#check @disabled_durable_check_skips_reader_after_capacity_and_freshness
#print axioms disabled_durable_check_skips_reader_after_capacity_and_freshness
set_option pp.all true in
#check @enabled_durable_check_returns_exact_reader_result_after_prior_checks
#print axioms enabled_durable_check_returns_exact_reader_result_after_prior_checks
set_option pp.all true in
#check @returned_admission_derives_natural_capacity_freshness_and_required_reader_success
#print axioms returned_admission_derives_natural_capacity_freshness_and_required_reader_success
set_option pp.all true in
#check @returned_whole_stage_derives_prior_typed_branch_all_checks_and_exact_original_field_append
#print axioms returned_whole_stage_derives_prior_typed_branch_all_checks_and_exact_original_field_append
end ShielddSecurity.TransferWordStageAdmission01
