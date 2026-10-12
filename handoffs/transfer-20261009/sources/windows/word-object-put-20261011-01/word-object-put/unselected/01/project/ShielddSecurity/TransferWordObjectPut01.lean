import ShielddSecurity.TransferWordLayerFlatten01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWordObjectPut01
open TransferStateDelta (View Writes overlay)
open TransferCanonicalWordPending01 (WordNativePending encodeWordPending)
open TransferWordObjectCodec01 (WordTaggedObject)
/-! Fixed PendingNullifierBlock object_put checks previous underlying Any
type identity before inserting a boxed pending value. Bool denotes whether
that TypeId is the pending enum's type, not a concrete Rust TypeId. Existing
Open and Sealed values share this type. Wrong type is a non-returning panic
sentinel. Native TypeId/boxing/Clone/map/lock/compiler correspondence remains
explicit. This model adds no native or executed control/certification credit. -/

def pendingTypeMatch {Other : Type} : Option (WordTaggedObject Other) → Option Bool
  | none => none
  | some (.inl _) => some true
  | some (.inr _) => some false

def checkedPendingPut {Other : Type} (previous : Option (WordTaggedObject Other)) (fields : WordNativePending) :
    Except Unit (WordTaggedObject Other) :=
  if pendingTypeMatch previous = some false then .error () else .ok (.inl fields)

def checkedPutAtKey {Other : Type} (parent : View (WordTaggedObject Other))
    (writes : Writes (WordTaggedObject Other)) (key : Nat) (fields : WordNativePending) :
    Except Unit (Writes (WordTaggedObject Other)) :=
  (checkedPendingPut ((overlay parent writes) key) fields).map
    (fun object other => if other = key then some (some object) else writes other)

theorem absent_or_tombstoned_slot_allows_pending_type_insert {Other : Type} (fields : WordNativePending) :
    checkedPendingPut (Other := Other) none fields = .ok (.inl fields) := rfl

theorem previous_open_or_sealed_pending_enum_allows_same_type_insert {Other : Type}
    (previous fields : WordNativePending) :
    checkedPendingPut (Other := Other) (some (.inl previous)) fields = .ok (.inl fields) := rfl

theorem previous_other_type_panics_before_pending_insert {Other : Type} (other : Other) (fields : WordNativePending) :
    checkedPendingPut (some (.inr other)) fields = .error () := rfl

theorem returned_checked_pending_put_derives_exact_latest_write_and_frames_other_keys {Other : Type}
    (parent : View (WordTaggedObject Other)) (writes updated : Writes (WordTaggedObject Other))
    (key : Nat) (fields : WordNativePending) (returned : checkedPutAtKey parent writes key fields = .ok updated) :
    updated key = some (some (.inl fields)) ∧ ∀ other, other ≠ key → updated other = writes other := by
  have same : (fun other => if other = key then some (some (Sum.inl fields : WordTaggedObject Other)) else writes other) = updated := by
    cases selected : (overlay parent writes) key with
    | none =>
      simp only [checkedPutAtKey, selected] at returned
      exact Except.ok.inj returned
    | some object =>
      cases object with
      | inl previous =>
        simp only [checkedPutAtKey, selected] at returned
        exact Except.ok.inj returned
      | inr other =>
        simp only [checkedPutAtKey, selected] at returned
        cases returned
  rw [← same]
  exact ⟨by simp only [ite_true], fun other different => by simp only [if_neg different]⟩

theorem returned_supported_sealed_put_derives_successful_checked_object_read {Other : Type}
    (parent : View (WordTaggedObject Other)) (writes updated : Writes (WordTaggedObject Other))
    (key : Nat) (ordered : List Nat) (capacity : ordered.length ≤ TransferNullifierConsensusLimits01.blockCapacity)
    (canonical : ∀ value ∈ ordered, value < TransferBoundedNativeCodec01.nullifierModulus)
    (returned : checkedPutAtKey parent writes key (encodeWordPending (.sealed ordered)) = .ok updated) :
    TransferWordObjectRead01.sourcePending ((overlay parent updated) key) = .ok (.sealed ordered) := by
  have write := (returned_checked_pending_put_derives_exact_latest_write_and_frames_other_keys parent writes updated key
    (encodeWordPending (.sealed ordered)) returned).1
  simp only [overlay, write]
  exact TransferWordObjectRead01.canonical_bounded_sealed_object_checked_read_recovers_exact_pending ordered capacity canonical

set_option pp.all true in
#check @pendingTypeMatch
#print axioms pendingTypeMatch
set_option pp.all true in
#check @checkedPendingPut
#print axioms checkedPendingPut
set_option pp.all true in
#check @checkedPutAtKey
#print axioms checkedPutAtKey
set_option pp.all true in
#check @absent_or_tombstoned_slot_allows_pending_type_insert
#print axioms absent_or_tombstoned_slot_allows_pending_type_insert
set_option pp.all true in
#check @previous_open_or_sealed_pending_enum_allows_same_type_insert
#print axioms previous_open_or_sealed_pending_enum_allows_same_type_insert
set_option pp.all true in
#check @previous_other_type_panics_before_pending_insert
#print axioms previous_other_type_panics_before_pending_insert
set_option pp.all true in
#check @returned_checked_pending_put_derives_exact_latest_write_and_frames_other_keys
#print axioms returned_checked_pending_put_derives_exact_latest_write_and_frames_other_keys
set_option pp.all true in
#check @returned_supported_sealed_put_derives_successful_checked_object_read
#print axioms returned_supported_sealed_put_derives_successful_checked_object_read
end ShielddSecurity.TransferWordObjectPut01
