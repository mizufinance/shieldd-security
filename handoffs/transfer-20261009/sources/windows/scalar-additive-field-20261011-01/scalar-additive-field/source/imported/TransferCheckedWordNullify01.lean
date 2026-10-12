import ShielddSecurity.TransferCheckedWordSealPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCheckedWordNullify01
open TransferStateDelta (View Writes overlay Delta)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferNullifierBatchSource01 (Backend BatchError)
open TransferWordStageCachePublication01 (stageAtKey)
/-! Public source nullify_all skips every pending read for empty inputs,
otherwise requires a transaction source before checked source staging. These
guards precede type checking and reader invocation. Functional live state and
native source selector/cache/Any/collection/reader/compiler bindings remain
OPEN; no runtime/control/replay/certification credit. -/

def nullifyAtKey {O E Other : Type} (backend : Backend O E) (child : Delta O E)
    (parent : View (WordTaggedObject Other)) (writes : Writes (WordTaggedObject Other))
    (key : Nat) (inputs : List CanonicalScalar) (sourceHasId : Bool) :
    Except Unit (Except BatchError (Writes (WordTaggedObject Other))) :=
  if inputs.isEmpty then .ok (.ok writes)
  else if sourceHasId then stageAtKey backend child parent writes key inputs
  else .ok (.error .source)

theorem empty_public_batch_skips_source_type_and_all_reads {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes : Writes (WordTaggedObject Other)) (key : Nat) (sourceHasId : Bool) :
    nullifyAtKey backend child parent writes key [] sourceHasId = .ok (.ok writes) := rfl

theorem nonempty_missing_source_returns_refusal_before_type_and_reader {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes : Writes (WordTaggedObject Other)) (key : Nat) (inputs : List CanonicalScalar)
    (nonempty : inputs.isEmpty = false) :
    nullifyAtKey backend child parent writes key inputs false = .ok (.error .source) := by
  simp only [nullifyAtKey, nonempty, Bool.false_eq_true, if_false]

theorem nonempty_present_source_forwards_exact_checked_stage {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes : Writes (WordTaggedObject Other)) (key : Nat) (inputs : List CanonicalScalar)
    (nonempty : inputs.isEmpty = false) :
    nullifyAtKey backend child parent writes key inputs true = stageAtKey backend child parent writes key inputs := by
  simp only [nullifyAtKey, nonempty, Bool.false_eq_true, if_false, if_true]

theorem returned_nonempty_public_batch_derives_source_and_actual_checked_stage {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes next : Writes (WordTaggedObject Other)) (key : Nat) (inputs : List CanonicalScalar) (sourceHasId : Bool)
    (nonempty : inputs.isEmpty = false)
    (returned : nullifyAtKey backend child parent writes key inputs sourceHasId = .ok (.ok next)) :
    sourceHasId = true ∧ stageAtKey backend child parent writes key inputs = .ok (.ok next) := by
  simp only [nullifyAtKey, nonempty, Bool.false_eq_true, if_false] at returned
  cases sourceHasId with
  | false => cases returned
  | true => exact ⟨rfl, returned⟩

theorem returned_public_batch_derives_empty_identity_or_nonempty_source_and_stage {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes next : Writes (WordTaggedObject Other)) (key : Nat) (inputs : List CanonicalScalar) (sourceHasId : Bool)
    (returned : nullifyAtKey backend child parent writes key inputs sourceHasId = .ok (.ok next)) :
    (inputs = [] ∧ next = writes) ∨
      (inputs.isEmpty = false ∧ sourceHasId = true ∧ stageAtKey backend child parent writes key inputs = .ok (.ok next)) := by
  cases inputs with
  | nil =>
    exact Or.inl ⟨rfl, (Except.ok.inj (Except.ok.inj returned)).symm⟩
  | cons first rest =>
    obtain ⟨source, staged⟩ := returned_nonempty_public_batch_derives_source_and_actual_checked_stage
      backend child parent writes next key (first :: rest) sourceHasId rfl returned
    exact Or.inr ⟨rfl, source, staged⟩

set_option pp.all true in
#check @nullifyAtKey
#print axioms nullifyAtKey
set_option pp.all true in
#check @empty_public_batch_skips_source_type_and_all_reads
#print axioms empty_public_batch_skips_source_type_and_all_reads
set_option pp.all true in
#check @nonempty_missing_source_returns_refusal_before_type_and_reader
#print axioms nonempty_missing_source_returns_refusal_before_type_and_reader
set_option pp.all true in
#check @nonempty_present_source_forwards_exact_checked_stage
#print axioms nonempty_present_source_forwards_exact_checked_stage
set_option pp.all true in
#check @returned_nonempty_public_batch_derives_source_and_actual_checked_stage
#print axioms returned_nonempty_public_batch_derives_source_and_actual_checked_stage
set_option pp.all true in
#check @returned_public_batch_derives_empty_identity_or_nonempty_source_and_stage
#print axioms returned_public_batch_derives_empty_identity_or_nonempty_source_and_stage
end ShielddSecurity.TransferCheckedWordNullify01
