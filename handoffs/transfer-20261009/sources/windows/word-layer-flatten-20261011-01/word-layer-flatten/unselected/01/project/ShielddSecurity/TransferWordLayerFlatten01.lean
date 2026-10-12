import ShielddSecurity.TransferWordLayeredObjectRead01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWordLayerFlatten01
open TransferStateDelta
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferWordLayeredObjectRead01 (checkedLayers selectedLiveLayers)
open TransferWordObjectRead01 (sourcePending)
/-! Symbolic newest-first checked lookup is joined to the original functional
oldest-first layer application and flatten recurrence. All live layers are
constructed as Some; no selected object or successful typed read is supplied.
The resulting getter can still panic on a selected wrong type. Native layer
liveness/locks/Clone/Any/ownership/concurrency/compiler bindings remain explicit.
No ancestor replay, native or executed control/certification credit. -/

theorem selected_live_layer_prefix_composes_with_older_stack {Other : Type}
    (newer older : List (Writes (WordTaggedObject Other))) (parent : View (WordTaggedObject Other)) (key : Nat) :
    selectedLiveLayers (newer ++ older) parent key =
      selectedLiveLayers newer (fun k => selectedLiveLayers older parent k) key := by
  induction newer with
  | nil => rfl
  | cons layer rest ih =>
    cases selected : layer key with
    | none => simpa only [List.cons_append, selectedLiveLayers, selected] using ih
    | some value => simp only [List.cons_append, selectedLiveLayers, selected]

theorem reverse_live_object_lookup_is_exact_oldest_first_layer_application {Other E : Type}
    (layers : List (Cache (WordTaggedObject Other) E)) (parent : State (WordTaggedObject Other)) (key : Nat) :
    selectedLiveLayers ((layers.map (fun layer => layer.objects)).reverse) parent.objects key =
      (applyLayers parent layers).objects key := by
  induction layers generalizing parent with
  | nil => rfl
  | cons layer rest ih =>
    rw [List.map_cons, List.reverse_cons, selected_live_layer_prefix_composes_with_older_stack]
    change selectedLiveLayers ((rest.map (fun item => item.objects)).reverse)
      (applyCache parent layer).objects key = (applyLayers (applyCache parent layer) rest).objects key
    exact ih (applyCache parent layer)

theorem live_checked_stack_agrees_with_functional_layer_object_observation {Other E : Type}
    (layers : List (Cache (WordTaggedObject Other) E)) (parent : State (WordTaggedObject Other)) (key : Nat) :
    checkedLayers (((layers.map (fun layer => layer.objects)).reverse).map some) (some parent.objects) key =
      sourcePending ((applyLayers parent layers).objects key) := by
  rw [TransferWordLayeredObjectRead01.live_checked_stack_reads_exact_newest_selected_entry,
    reverse_live_object_lookup_is_exact_oldest_first_layer_application]

theorem live_checked_stack_agrees_with_exact_functional_flatten_object {Other E : Type}
    (layers : List (Cache (WordTaggedObject Other) E)) (parent : State (WordTaggedObject Other)) (key : Nat) :
    checkedLayers (((layers.map (fun layer => layer.objects)).reverse).map some) (some parent.objects) key =
      sourcePending ((applyCache parent (flatten empty layers)).objects key) := by
  have flat := flatten_applies_in_order parent layers (empty : Cache (WordTaggedObject Other) E)
  rw [apply_empty] at flat
  rw [flat]
  exact live_checked_stack_agrees_with_functional_layer_object_observation layers parent key

set_option pp.all true in
#check @selected_live_layer_prefix_composes_with_older_stack
#print axioms selected_live_layer_prefix_composes_with_older_stack
set_option pp.all true in
#check @reverse_live_object_lookup_is_exact_oldest_first_layer_application
#print axioms reverse_live_object_lookup_is_exact_oldest_first_layer_application
set_option pp.all true in
#check @live_checked_stack_agrees_with_functional_layer_object_observation
#print axioms live_checked_stack_agrees_with_functional_layer_object_observation
set_option pp.all true in
#check @live_checked_stack_agrees_with_exact_functional_flatten_object
#print axioms live_checked_stack_agrees_with_exact_functional_flatten_object
end ShielddSecurity.TransferWordLayerFlatten01
