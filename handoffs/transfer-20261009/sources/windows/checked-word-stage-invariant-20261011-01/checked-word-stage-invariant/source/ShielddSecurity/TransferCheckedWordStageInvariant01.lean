import ShielddSecurity.TransferCheckedWordNullify01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCheckedWordStageInvariant01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
open TransferStateDelta (Delta)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferNullifierBatchSource01 (Backend inspect)
open TransferWordStageOrder01 (stageFields)
open TransferCheckedWordStageRefinement01 (checkedNumericStage readerForPrevious previousPending projectObjectPending)
open TransferPendingSetInvariant01 (Coherent Invariant)
open TransferNullifierConsensusLimits01 (blockCapacity)
/-! Successful checked source staging derives actual numeric inspection and
propagates its symbolic ordered/membership invariant. Prior coherence and
uniqueness are inductive state invariants, not a desired result or a getter,
type-domain, reader-success or codec-inverse assumption. Native bindings OPEN. -/

theorem returned_checked_source_stage_derives_actual_numeric_inspection {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (previous : Option (WordTaggedObject Other))
    (inputs : List CanonicalScalar) (object : WordTaggedObject Other)
    (returned : stageFields previous inputs true
      (readerForPrevious (backend.readerGate child) (backend.lookup child) previous) = .ok (.ok object)) :
    inspect {backend with pending := fun _ => previousPending previous} (2 ^ 64 - 1) blockCapacity
      child (inputs.map (fun scalar => scalarKey scalar.words)) = .ok (projectObjectPending object) := by
  have numeric := TransferCheckedWordStageRefinement01.returned_checked_source_stage_derives_successful_projected_numeric_stage
    backend child previous inputs object returned
  obtain ⟨unique, _⟩ := TransferWordStageAdmission01.returned_whole_stage_derives_prior_typed_branch_all_checks_and_exact_original_field_append
    previous inputs true (readerForPrevious (backend.readerGate child) (backend.lookup child) previous) object returned
  unfold checkedNumericStage at numeric
  dsimp only at numeric
  rw [unique] at numeric
  simp only [if_true] at numeric
  cases checked : TransferWordObjectRead01.checkedObject previous with
  | error panic => rw [checked] at numeric; cases numeric
  | ok pending => rw [checked] at numeric; exact Except.ok.inj numeric

theorem returned_checked_source_stage_preserves_numeric_invariant_and_exact_ordered_append {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (previous : Option (WordTaggedObject Other))
    (inputs : List CanonicalScalar) (object : WordTaggedObject Other)
    (coherent : Coherent (previousPending previous))
    (oldNodup : (previousPending previous).ordered.Nodup)
    (returned : stageFields previous inputs true
      (readerForPrevious (backend.readerGate child) (backend.lookup child) previous) = .ok (.ok object)) :
    Invariant blockCapacity (projectObjectPending object) ∧
      (projectObjectPending object).ordered = (previousPending previous).ordered ++ inputs.map (fun scalar => scalarKey scalar.words) ∧
      ∀ key ∈ inputs.map (fun scalar => scalarKey scalar.words), backend.lookup child key = some false := by
  have inspected := returned_checked_source_stage_derives_actual_numeric_inspection backend child previous inputs object returned
  have below : blockCapacity < 2 ^ 64 - 1 := by decide
  have invariant := TransferPendingSetInvariant01.successful_inspection_preserves_invariant
    {backend with pending := fun _ => previousPending previous} (2 ^ 64 - 1) blockCapacity child
    (inputs.map (fun scalar => scalarKey scalar.words)) (projectObjectPending object) coherent oldNodup below inspected
  have bounded := TransferNullifierBatchSource01.inspection_success_capacity_and_all_inputs
    {backend with pending := fun _ => previousPending previous} (2 ^ 64 - 1) blockCapacity child
    (inputs.map (fun scalar => scalarKey scalar.words)) (projectObjectPending object) below inspected
  exact ⟨invariant, bounded.1, fun key inside => (bounded.2.2.2 key inside).1⟩

set_option pp.all true in
#check @returned_checked_source_stage_derives_actual_numeric_inspection
#print axioms returned_checked_source_stage_derives_actual_numeric_inspection
set_option pp.all true in
#check @returned_checked_source_stage_preserves_numeric_invariant_and_exact_ordered_append
#print axioms returned_checked_source_stage_preserves_numeric_invariant_and_exact_ordered_append
end ShielddSecurity.TransferCheckedWordStageInvariant01
