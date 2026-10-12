import ShielddSecurity.TransferWordStageAdmission01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWordStageNumericRefinement01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
open TransferStateDelta
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferCanonicalWordPending01 (decodeWordPending)
open TransferPendingFiniteCodec01 (restore)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferNullifierBatchSource01 (Backend Pending BatchError inspect appendPending)
open TransferNullifierReaderVector01 (contains zipUnspent)
open TransferWordStageOrder01 (stageFields appendAfterCheckedRead admitOpen)
open TransferCanonicalSourceMembership01 (sourceOrdContains)
open TransferNullifierConsensusLimits01 (blockCapacity)
/-! Typed Open staging is compared to the existing numeric inspection with
concrete source-key pending projection and existing modeled durable reader.
Every refusal and returned append agrees, without a caller codec inverse,
admitted result, desired next object or successful getter premise. The prior
object is explicitly the typed Open constructor, not an arbitrary native Any.
Successful typed stage derives native-model inspection, exact append and all
authenticated-lookup unspent observations. Actual reader/Scalar/Ord/Any/usize/
compiler/async/delta and complete trace correspondence remain OPEN; no native,
executed control, certification or accepted ancestor replay credit. -/

def installTypedPending {O E : Type} (backend : Backend O E) (ordered members : List CanonicalScalar) : Backend O E :=
  {backend with pending := fun _ => restore (decodeWordPending (.opened ordered members))}

def typedDurableReader (gate : Bool) (lookup : Nat → Option Bool) (members : List CanonicalScalar)
    (inputs : List CanonicalScalar) : Except BatchError Unit :=
  let keys := inputs.map (fun scalar => scalarKey scalar.words)
  match contains gate lookup (fun key => (members.map (fun scalar => scalarKey scalar.words)).contains key) keys with
  | none => .error .reader
  | some flags => if zipUnspent keys flags then .ok () else .error .spent

theorem original_field_pending_freshness_equals_numeric_pending_freshness
    (members inputs : List CanonicalScalar) :
    inputs.all (fun scalar => !sourceOrdContains members scalar) =
      (inputs.map (fun scalar => scalarKey scalar.words)).all
        (fun key => !(members.map (fun scalar => scalarKey scalar.words)).contains key) := by
  rw [List.all_map]
  exact List.all_congr rfl (fun scalar => congrArg Bool.not
    (TransferCanonicalSourceMembership01.source_ord_membership_is_exact_mapped_key_membership members scalar))

theorem typed_open_stage_has_exact_numeric_inspection_result_and_original_field_write {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (ordered members inputs : List CanonicalScalar) :
    stageFields (Other := Other) (some (.inl (.opened ordered members))) inputs true
      (typedDurableReader (backend.readerGate child) (backend.lookup child) members) =
      .ok ((inspect (installTypedPending backend ordered members) (2 ^ 64 - 1) blockCapacity child
        (inputs.map (fun scalar => scalarKey scalar.words))).map
          (fun _ => (.inl (.opened (ordered ++ inputs) (members ++ inputs)) : WordTaggedObject Other))) := by
  simp only [stageFields, appendAfterCheckedRead, TransferWordObjectRead01.checkedObject, Option.getD_some,
    admitOpen, inspect, installTypedPending, decodeWordPending, restore, List.length_map,
    TransferPendingSaturatingCapacity01.sourceSaturatingLengthAdd, Bool.false_eq_true, if_false, Bool.true_eq_true, if_true]
  rw [original_field_pending_freshness_equals_numeric_pending_freshness]
  cases unique : TransferNullifierBatchSource01.uniqueLoop [] (inputs.map (fun scalar => scalarKey scalar.words)) with
  | false => simp only [unique, Bool.false_eq_true, if_false]; rfl
  | true =>
    simp only [unique, Bool.true_eq_true, if_true]
    by_cases capacity : min (ordered.length + inputs.length) (2 ^ 64 - 1) ≤ blockCapacity
    · simp only [if_pos capacity]
      cases fresh : (inputs.map (fun scalar => scalarKey scalar.words)).all
          (fun key => !(members.map (fun scalar => scalarKey scalar.words)).contains key) with
      | false => simp only [fresh, Bool.false_eq_true, if_false] <;> rfl
      | true =>
        simp only [fresh, Bool.true_eq_true, if_true]
        unfold typedDurableReader
        cases observed : contains (backend.readerGate child) (backend.lookup child)
            (fun key => (members.map (fun scalar => scalarKey scalar.words)).contains key)
            (inputs.map (fun scalar => scalarKey scalar.words)) with
        | none => simp only [observed] <;> rfl
        | some flags =>
          simp only [observed]
          cases unspent : zipUnspent (inputs.map (fun scalar => scalarKey scalar.words)) flags <;>
            simp only [unspent, Bool.false_eq_true, if_false, Bool.true_eq_true, if_true] <;> rfl
    · simp only [if_neg capacity] <;> rfl

theorem returned_typed_open_stage_derives_exact_numeric_pending_append {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (ordered members inputs : List CanonicalScalar)
    (object : WordTaggedObject Other)
    (returned : stageFields (some (.inl (.opened ordered members))) inputs true
      (typedDurableReader (backend.readerGate child) (backend.lookup child) members) = .ok (.ok object)) :
    ∃ next : Pending,
      inspect (installTypedPending backend ordered members) (2 ^ 64 - 1) blockCapacity child
        (inputs.map (fun scalar => scalarKey scalar.words)) = .ok next ∧
      next = appendPending (restore (decodeWordPending (.opened ordered members)))
        (inputs.map (fun scalar => scalarKey scalar.words)) := by
  rw [typed_open_stage_has_exact_numeric_inspection_result_and_original_field_write] at returned
  have mapped := Except.ok.inj returned
  cases inspected : inspect (installTypedPending backend ordered members) (2 ^ 64 - 1) blockCapacity child
      (inputs.map (fun scalar => scalarKey scalar.words)) with
  | error refusal => simp only [inspected, Except.map] at mapped; cases mapped
  | ok next =>
    obtain ⟨previous, _, previousEq, _, _, _, _, _, _, nextEq⟩ :=
      TransferNullifierBatchSource01.inspection_success_order (installTypedPending backend ordered members)
        (2 ^ 64 - 1) blockCapacity child (inputs.map (fun scalar => scalarKey scalar.words)) next inspected
    exact ⟨next, inspected, nextEq.trans (congrArg
      (fun pending : Pending => appendPending pending (inputs.map (fun scalar => scalarKey scalar.words))) previousEq)⟩

theorem returned_typed_open_stage_derives_actual_lookup_unspent_and_pending_freshness {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (ordered members inputs : List CanonicalScalar)
    (object : WordTaggedObject Other)
    (returned : stageFields (some (.inl (.opened ordered members))) inputs true
      (typedDurableReader (backend.readerGate child) (backend.lookup child) members) = .ok (.ok object)) :
    ∀ key ∈ inputs.map (fun scalar => scalarKey scalar.words),
      backend.lookup child key = some false ∧
        (members.map (fun scalar => scalarKey scalar.words)).contains key = false := by
  obtain ⟨next, inspected, _⟩ := returned_typed_open_stage_derives_exact_numeric_pending_append
    backend child ordered members inputs object returned
  have allInputs := TransferNullifierBatchSource01.inspection_success_capacity_and_all_inputs
    (installTypedPending backend ordered members) (2 ^ 64 - 1) blockCapacity child
    (inputs.map (fun scalar => scalarKey scalar.words)) next
    TransferPendingSaturatingCapacity01.consensus_capacity_has_strict_32_and_64_bit_saturation_headroom.2 inspected
  intro key inside
  have facts := allInputs.2.2.2 key inside
  exact ⟨facts.1, facts.2.1⟩

set_option pp.all true in
#check @installTypedPending
#print axioms installTypedPending
set_option pp.all true in
#check @typedDurableReader
#print axioms typedDurableReader
set_option pp.all true in
#check @original_field_pending_freshness_equals_numeric_pending_freshness
#print axioms original_field_pending_freshness_equals_numeric_pending_freshness
set_option pp.all true in
#check @typed_open_stage_has_exact_numeric_inspection_result_and_original_field_write
#print axioms typed_open_stage_has_exact_numeric_inspection_result_and_original_field_write
set_option pp.all true in
#check @returned_typed_open_stage_derives_exact_numeric_pending_append
#print axioms returned_typed_open_stage_derives_exact_numeric_pending_append
set_option pp.all true in
#check @returned_typed_open_stage_derives_actual_lookup_unspent_and_pending_freshness
#print axioms returned_typed_open_stage_derives_actual_lookup_unspent_and_pending_freshness
end ShielddSecurity.TransferWordStageNumericRefinement01
