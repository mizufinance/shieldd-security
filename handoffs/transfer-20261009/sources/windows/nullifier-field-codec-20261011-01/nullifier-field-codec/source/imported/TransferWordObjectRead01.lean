import ShielddSecurity.TransferWordSourceDriver01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWordObjectRead01
open TransferStateDelta (View Writes overlay)
open TransferWordObjectCodec01 (WordTaggedObject encodeNative decodeNative)
open TransferCanonicalWordPending01 (WordNativePending decodeWordPending)
open TransferPendingFiniteCodec01 (NativePending)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Source-shaped checked typed getter. The error unit is a panic sentinel
for present wrong-type downcast, outside the returned Rust Result model.
Only absence/tombstone defaults. Native Any/TypeId/Clone/locks/layers/compiler
correspondence remains explicit. No executed refusal/control/native credit. -/

def checkedObject {Other : Type} : Option (WordTaggedObject Other) → Except Unit (Option WordNativePending)
  | none => .ok none
  | some (.inl fields) => .ok (some fields)
  | some (.inr _) => .error ()

def defaultPending : Option WordNativePending → NativePending
  | none => .opened [] []
  | some fields => decodeWordPending fields

def sourcePending {Other : Type} (object : Option (WordTaggedObject Other)) : Except Unit NativePending :=
  (checkedObject object).map defaultPending

theorem absent_or_tombstone_reaches_empty_pending_default {Other : Type} :
    sourcePending (Other := Other) none = .ok (.opened [] []) := rfl

theorem present_wrong_type_cannot_reach_empty_default {Other : Type} (other : Other) :
    sourcePending (some (.inr other)) = .error () ∧
      sourcePending (some (.inr other)) ≠ .ok (.opened [] []) := by
  exact ⟨rfl, by intro impossible; cases impossible⟩

theorem canonical_bounded_sealed_object_checked_read_recovers_exact_pending {Other : Type}
    (ordered : List Nat) (capacity : ordered.length ≤ blockCapacity)
    (canonical : ∀ key ∈ ordered, key < nullifierModulus) :
    sourcePending (some (encodeNative (Other := Other) (.sealed ordered))) = .ok (.sealed ordered) := by
  have supported : TransferBoundedNativeCodec01.nativeSupported (.sealed ordered) = true := by
    simp only [TransferBoundedNativeCodec01.nativeSupported, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨capacity, canonical⟩
  change Except.ok (decodeNative (encodeNative (Other := Other) (.sealed ordered))) = Except.ok (.sealed ordered)
  exact congrArg Except.ok (TransferWordObjectCodec01.supported_word_object_codec_recovers_exact_finite_native_enum (.sealed ordered) supported)

theorem successful_checked_getter_agrees_with_existing_projection_only_on_success {Other : Type}
    (object : Option (WordTaggedObject Other)) (pending : NativePending)
    (returned : sourcePending object = .ok pending) :
    pending = (object.map decodeNative).getD (.opened [] []) := by
  cases object with
  | none =>
    exact (Except.ok.inj returned).symm
  | some object =>
    cases object with
    | inl fields => exact (Except.ok.inj returned).symm
    | inr other => cases returned

theorem checked_object_overlay_uses_latest_entry_without_typed_fallback {Other : Type}
    (parent : View (WordTaggedObject Other)) (writes : Writes (WordTaggedObject Other)) (key : Nat) :
    sourcePending ((overlay parent writes) key) =
      match writes key with
      | none => sourcePending (parent key)
      | some value => sourcePending value := by
  cases selected : writes key <;> simp only [overlay, selected]

set_option pp.all true in
#check @checkedObject
#print axioms checkedObject
set_option pp.all true in
#check @defaultPending
#print axioms defaultPending
set_option pp.all true in
#check @sourcePending
#print axioms sourcePending
set_option pp.all true in
#check @absent_or_tombstone_reaches_empty_pending_default
#print axioms absent_or_tombstone_reaches_empty_pending_default
set_option pp.all true in
#check @present_wrong_type_cannot_reach_empty_default
#print axioms present_wrong_type_cannot_reach_empty_default
set_option pp.all true in
#check @canonical_bounded_sealed_object_checked_read_recovers_exact_pending
#print axioms canonical_bounded_sealed_object_checked_read_recovers_exact_pending
set_option pp.all true in
#check @successful_checked_getter_agrees_with_existing_projection_only_on_success
#print axioms successful_checked_getter_agrees_with_existing_projection_only_on_success
set_option pp.all true in
#check @checked_object_overlay_uses_latest_entry_without_typed_fallback
#print axioms checked_object_overlay_uses_latest_entry_without_typed_fallback
end ShielddSecurity.TransferWordObjectRead01
