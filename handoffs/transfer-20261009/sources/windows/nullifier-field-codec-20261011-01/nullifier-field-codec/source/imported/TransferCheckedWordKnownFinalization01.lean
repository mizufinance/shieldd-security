import ShielddSecurity.TransferCheckedWordBlockDriver01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCheckedWordKnownFinalization01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
open TransferStateDelta (View Writes overlay Delta State Cache Bytes applyCache)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferNullifierBatchSource01 (Backend)
open TransferCheckedWordBlockDriver01 (run allFields)
open TransferWordSctPendingRead01 (sourceOrdered sourceIsSealed sourceEnsureSealed)
open TransferFinalizationObjectFrames01 (Mutation mutationWalk)
open TransferInjectiveKeyPublication01 (keyCode)
open TransferNullifierObjectKeys01 (nullifierBytes)
/-! Actual returned checked-word block getter survives the six known source-
ordered post-seal object mutations, including tombstone deletes. This composes
the derived word object with the prior source-ordered recipe and symbolic frame
theorem. The recipe covers known operations only; all hidden native callees,
tree values, complete App trace/Any/Clone/ownership/compiler bindings are OPEN.
No exhaustive native trace or replay/control/certification credit. -/

def wordMutations {Other : Type} (tree : WordTaggedObject Other) : List (Mutation (WordTaggedObject Other)) :=
  (TransferSourceOrderedFinalizer01.fixedMutations tree).map fun mutation =>
    ⟨mutation.key, mutation.permitted,
      mutation.value.bind (fun value => match value with | .inl object => some object | .inr _ => none)⟩

def selectedDelta {O E Other : Type} (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes : Writes (WordTaggedObject Other)) : Delta (WordTaggedObject Other) E :=
  ⟨⟨child.parent.verifiable, child.parent.nonverifiable, parent⟩,
    ⟨child.cache.verifiable, child.cache.nonverifiable, writes, child.cache.events⟩⟩

theorem known_word_mutations_have_exact_corrected_source_key_order {Other : Type} (tree : WordTaggedObject Other) :
    (wordMutations tree).map (fun mutation => mutation.key) =
      (TransferSourceOrderedFinalizer01.fixedMutations tree).map (fun mutation => mutation.key) := by
  rw [wordMutations, List.map_map]
  rfl

theorem known_word_mutations_contain_only_exact_tree_put_and_deletion_tombstones {Other : Type} (tree : WordTaggedObject Other) :
    (wordMutations tree).map (fun mutation => mutation.value) = [none, some tree, none, none, none, none] := rfl

theorem returned_checked_word_block_survives_known_source_ordered_finishing_mutations {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes final : Writes (WordTaggedObject Other)) (batches : List (List CanonicalScalar × Bool))
    (tree : WordTaggedObject Other)
    (initiallyAbsent : (overlay parent writes) (keyCode nullifierBytes) = none)
    (returned : run backend child parent writes (keyCode nullifierBytes) batches = .ok (.ok final)) :
    let finished := mutationWalk keyCode (selectedDelta child parent final) (wordMutations tree)
    (applyCache finished.parent finished.cache).objects (keyCode nullifierBytes) =
      some (.inl (.sealed (allFields batches))) ∧
      sourceOrdered ((applyCache finished.parent finished.cache).objects (keyCode nullifierBytes)) = .ok (allFields batches) ∧
      sourceIsSealed ((applyCache finished.parent finished.cache).objects (keyCode nullifierBytes)) = .ok true ∧
      sourceEnsureSealed ((applyCache finished.parent finished.cache).objects (keyCode nullifierBytes)) = .ok (.ok ()) := by
  obtain ⟨actual, _, _, _, _, _, _, _⟩ :=
    TransferCheckedWordBlockDriver01.returned_whole_checked_block_derives_actual_exact_original_global_field_getter
      backend child parent writes final (keyCode nullifierBytes) batches initiallyAbsent returned
  have preserved := TransferFinalizationObjectFrames01.symbolic_known_finalization_mutation_walk_preserves_pending_observation
    keyCode TransferInjectiveKeyPublication01.keyCode_is_injective (selectedDelta child parent final) (wordMutations tree)
  have selected : (applyCache (selectedDelta child parent final).parent (selectedDelta child parent final).cache).objects
      (keyCode nullifierBytes) = some (.inl (.sealed (allFields batches))) := actual
  have reached := preserved.trans selected
  refine ⟨reached, ?_, ?_, ?_⟩
  · rw [reached]; rfl
  · rw [reached]; rfl
  · rw [reached]; rfl

set_option pp.all true in
#check @wordMutations
#print axioms wordMutations
set_option pp.all true in
#check @selectedDelta
#print axioms selectedDelta
set_option pp.all true in
#check @known_word_mutations_have_exact_corrected_source_key_order
#print axioms known_word_mutations_have_exact_corrected_source_key_order
set_option pp.all true in
#check @known_word_mutations_contain_only_exact_tree_put_and_deletion_tombstones
#print axioms known_word_mutations_contain_only_exact_tree_put_and_deletion_tombstones
set_option pp.all true in
#check @returned_checked_word_block_survives_known_source_ordered_finishing_mutations
#print axioms returned_checked_word_block_survives_known_source_ordered_finishing_mutations
end ShielddSecurity.TransferCheckedWordKnownFinalization01
