import ShielddSecurity.TransferPendingSaturatingCapacity01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWordLayeredObjectRead01
open TransferStateDelta (View Writes)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferWordObjectRead01 (sourcePending)
open TransferPendingFiniteCodec01 (NativePending)
/-! Native-source-shaped leaf then newest-to-oldest layer lookup. A missing
applied layer or parent is a panic sentinel, outside returned Rust Result.
Present tombstones and wrong types stop traversal, while a missing map entry
continues. Live stack recurrence is proved without a supplied selected value.
This finite model retains native Any/Clone/locks/alias/time/stack/compiler
correspondence separately; no executed control/native/certification credit. -/

def checkedLayers {Other : Type} : List (Option (Writes (WordTaggedObject Other))) →
    Option (View (WordTaggedObject Other)) → Nat → Except Unit NativePending
  | [], none, _ => .error ()
  | [], some parent, key => sourcePending (parent key)
  | none :: _, _, _ => .error ()
  | some layer :: rest, parent, key =>
    match layer key with
    | none => checkedLayers rest parent key
    | some value => sourcePending value

def selectedLiveLayers {Other : Type} : List (Writes (WordTaggedObject Other)) →
    View (WordTaggedObject Other) → Nat → Option (WordTaggedObject Other)
  | [], parent, key => parent key
  | layer :: rest, parent, key =>
    match layer key with
    | none => selectedLiveLayers rest parent key
    | some value => value

theorem live_checked_stack_reads_exact_newest_selected_entry {Other : Type}
    (layers : List (Writes (WordTaggedObject Other))) (parent : View (WordTaggedObject Other)) (key : Nat) :
    checkedLayers (layers.map some) (some parent) key = sourcePending (selectedLiveLayers layers parent key) := by
  induction layers with
  | nil => rfl
  | cons layer rest ih =>
    cases selected : layer key with
    | none => simpa only [List.map_cons, checkedLayers, selectedLiveLayers, selected] using ih
    | some value => simp only [List.map_cons, checkedLayers, selectedLiveLayers, selected]

theorem applied_leaf_panics_before_any_underlying_read {Other : Type}
    (rest : List (Option (Writes (WordTaggedObject Other)))) (parent : Option (View (WordTaggedObject Other))) (key : Nat) :
    checkedLayers (none :: rest) parent key = .error () := rfl

theorem live_leaf_tombstone_stops_before_underlying_and_defaults {Other : Type}
    (leaf : Writes (WordTaggedObject Other)) (rest : List (Option (Writes (WordTaggedObject Other))))
    (parent : Option (View (WordTaggedObject Other))) (key : Nat) (tombstone : leaf key = some none) :
    checkedLayers (some leaf :: rest) parent key = .ok (.opened [] []) := by
  simp only [checkedLayers, tombstone]
  rfl

theorem live_leaf_wrong_type_panics_without_older_typed_fallback {Other : Type}
    (leaf : Writes (WordTaggedObject Other)) (rest : List (Option (Writes (WordTaggedObject Other))))
    (parent : Option (View (WordTaggedObject Other))) (key : Nat) (other : Other)
    (wrongType : leaf key = some (some (.inr other))) :
    checkedLayers (some leaf :: rest) parent key = .error () := by
  simp only [checkedLayers, wrongType]
  rfl

theorem live_leaf_map_miss_continues_at_the_next_layer {Other : Type}
    (leaf : Writes (WordTaggedObject Other)) (rest : List (Option (Writes (WordTaggedObject Other))))
    (parent : Option (View (WordTaggedObject Other))) (key : Nat) (miss : leaf key = none) :
    checkedLayers (some leaf :: rest) parent key = checkedLayers rest parent key := by
  simp only [checkedLayers, miss]

theorem stack_fallback_panics_for_applied_parent_and_reads_live_parent {Other : Type}
    (parent : View (WordTaggedObject Other)) (key : Nat) :
    checkedLayers (Other := Other) [] none key = .error () ∧
      checkedLayers [] (some parent) key = sourcePending (parent key) := ⟨rfl, rfl⟩

set_option pp.all true in
#check @checkedLayers
#print axioms checkedLayers
set_option pp.all true in
#check @selectedLiveLayers
#print axioms selectedLiveLayers
set_option pp.all true in
#check @live_checked_stack_reads_exact_newest_selected_entry
#print axioms live_checked_stack_reads_exact_newest_selected_entry
set_option pp.all true in
#check @applied_leaf_panics_before_any_underlying_read
#print axioms applied_leaf_panics_before_any_underlying_read
set_option pp.all true in
#check @live_leaf_tombstone_stops_before_underlying_and_defaults
#print axioms live_leaf_tombstone_stops_before_underlying_and_defaults
set_option pp.all true in
#check @live_leaf_wrong_type_panics_without_older_typed_fallback
#print axioms live_leaf_wrong_type_panics_without_older_typed_fallback
set_option pp.all true in
#check @live_leaf_map_miss_continues_at_the_next_layer
#print axioms live_leaf_map_miss_continues_at_the_next_layer
set_option pp.all true in
#check @stack_fallback_panics_for_applied_parent_and_reads_live_parent
#print axioms stack_fallback_panics_for_applied_parent_and_reads_live_parent
end ShielddSecurity.TransferWordLayeredObjectRead01
