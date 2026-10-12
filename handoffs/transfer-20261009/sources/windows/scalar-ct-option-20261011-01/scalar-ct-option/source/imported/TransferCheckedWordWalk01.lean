import ShielddSecurity.TransferCheckedWordStageInvariant01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCheckedWordWalk01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
open TransferStateDelta (View Writes overlay Delta)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferNullifierBatchSource01 (Backend BatchError)
open TransferCheckedWordNullify01 (nullifyAtKey)
open TransferCheckedWordStageRefinement01 (previousPending readerForPrevious projectObjectPending)
open TransferPendingSetInvariant01 (Invariant)
open TransferNullifierConsensusLimits01 (blockCapacity)
/-! Symbolic public checked-word batch walk updates the actual functional
selected cache slot at each successful nonempty stage; empty batches retain
it. Returned success derives exact global source key order, coherence,
uniqueness, capacity, every durable false lookup and all other-key frames.
Native selector/cache/Any/Clone/imbl/Scalar/reader/compiler bindings OPEN. -/

def walk {O E Other : Type} (backend : Backend O E) (child : Delta O E)
    (parent : View (WordTaggedObject Other)) (key : Nat) :
    Writes (WordTaggedObject Other) → List (List CanonicalScalar × Bool) →
      Except Unit (Except BatchError (Writes (WordTaggedObject Other)))
  | writes, [] => .ok (.ok writes)
  | writes, batch :: rest =>
    (nullifyAtKey backend child parent writes key batch.1 batch.2).bind fun result =>
      match result with
      | .error error => .ok (.error error)
      | .ok next => walk backend child parent key next rest

theorem returned_cons_walk_derives_actual_first_batch_and_remaining_walk {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other)) (key : Nat)
    (writes final : Writes (WordTaggedObject Other)) (batch : List CanonicalScalar × Bool)
    (rest : List (List CanonicalScalar × Bool))
    (returned : walk backend child parent key writes (batch :: rest) = .ok (.ok final)) :
    ∃ next, nullifyAtKey backend child parent writes key batch.1 batch.2 = .ok (.ok next) ∧
      walk backend child parent key next rest = .ok (.ok final) := by
  unfold walk at returned
  cases first : nullifyAtKey backend child parent writes key batch.1 batch.2 with
  | error panic => rw [first] at returned; cases returned
  | ok result =>
    rw [first] at returned
    cases result with
    | error refusal => cases returned
    | ok next => exact ⟨next, rfl, returned⟩

theorem returned_public_batch_preserves_actual_slot_invariant_order_and_frames {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other)) (key : Nat)
    (writes next : Writes (WordTaggedObject Other)) (inputs : List CanonicalScalar) (sourceHasId : Bool)
    (invariant : Invariant blockCapacity (previousPending ((overlay parent writes) key)))
    (returned : nullifyAtKey backend child parent writes key inputs sourceHasId = .ok (.ok next)) :
    Invariant blockCapacity (previousPending ((overlay parent next) key)) ∧
      (previousPending ((overlay parent next) key)).ordered =
        (previousPending ((overlay parent writes) key)).ordered ++ inputs.map (fun scalar => scalarKey scalar.words) ∧
      (∀ nullifier ∈ inputs.map (fun scalar => scalarKey scalar.words), backend.lookup child nullifier = some false) ∧
      (∀ other, other ≠ key → next other = writes other) := by
  cases TransferCheckedWordNullify01.returned_public_batch_derives_empty_identity_or_nonempty_source_and_stage
      backend child parent writes next key inputs sourceHasId returned with
  | inl empty =>
    obtain ⟨nil, unchanged⟩ := empty
    subst inputs
    subst next
    refine ⟨invariant, ?_, ?_, fun _ _ => rfl⟩
    · simp only [List.map_nil, List.append_nil]
    · intro nullifier inside; cases inside
  | inr nonempty =>
    obtain ⟨_, _, stagedReturned⟩ := nonempty
    obtain ⟨object, staged, cached⟩ :=
      TransferWordStageCachePublication01.returned_stage_at_key_derives_exact_returned_object_and_one_cache_write
        backend child parent writes next key inputs stagedReturned
    obtain ⟨nextInvariant, appended, unspent⟩ :=
      TransferCheckedWordStageInvariant01.returned_checked_source_stage_preserves_numeric_invariant_and_exact_ordered_append
        backend child ((overlay parent writes) key) inputs object invariant.1 invariant.2.1 staged
    have atKey : next key = some (some object) := by
      rw [cached]
      exact if_pos rfl
    have selected : (overlay parent next) key = some object := by
      simp only [overlay, atKey]
    have projected : previousPending ((overlay parent next) key) = projectObjectPending object := by
      rw [selected]; rfl
    rw [projected]
    refine ⟨nextInvariant, appended, unspent, ?_⟩
    intro other different
    rw [cached]
    exact if_neg different

theorem returned_whole_walk_derives_global_order_invariant_unspent_and_frames {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other)) (key : Nat)
    (batches : List (List CanonicalScalar × Bool)) (writes final : Writes (WordTaggedObject Other))
    (invariant : Invariant blockCapacity (previousPending ((overlay parent writes) key)))
    (returned : walk backend child parent key writes batches = .ok (.ok final)) :
    Invariant blockCapacity (previousPending ((overlay parent final) key)) ∧
      (previousPending ((overlay parent final) key)).ordered =
        (previousPending ((overlay parent writes) key)).ordered ++
          batches.flatMap (fun batch => batch.1.map (fun scalar => scalarKey scalar.words)) ∧
      (∀ nullifier ∈ batches.flatMap (fun batch => batch.1.map (fun scalar => scalarKey scalar.words)),
        backend.lookup child nullifier = some false) ∧
      (∀ other, other ≠ key → final other = writes other ∧ (overlay parent final) other = (overlay parent writes) other) := by
  induction batches generalizing writes with
  | nil =>
    have unchanged : writes = final := Except.ok.inj (Except.ok.inj returned)
    subst final
    refine ⟨invariant, ?_, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    · simp only [List.flatMap_nil, List.append_nil]
    · intro nullifier inside; cases inside
  | cons batch rest ih =>
    obtain ⟨next, firstReturned, restReturned⟩ :=
      returned_cons_walk_derives_actual_first_batch_and_remaining_walk backend child parent key writes final batch rest returned
    obtain ⟨nextInvariant, firstOrder, firstUnspent, firstFrames⟩ :=
      returned_public_batch_preserves_actual_slot_invariant_order_and_frames
        backend child parent key writes next batch.1 batch.2 invariant firstReturned
    obtain ⟨finalInvariant, restOrder, restUnspent, restFrames⟩ := ih next nextInvariant restReturned
    refine ⟨finalInvariant, ?_, ?_, ?_⟩
    · rw [restOrder, firstOrder, List.flatMap_cons, List.append_assoc]
    · intro nullifier inside
      cases List.mem_append.mp inside with
      | inl first => exact firstUnspent nullifier first
      | inr later => exact restUnspent nullifier later
    · intro other different
      have framed := (restFrames other different).1.trans (firstFrames other different)
      refine ⟨framed, ?_⟩
      simp only [overlay, framed]

set_option pp.all true in
#check @walk
#print axioms walk
set_option pp.all true in
#check @returned_cons_walk_derives_actual_first_batch_and_remaining_walk
#print axioms returned_cons_walk_derives_actual_first_batch_and_remaining_walk
set_option pp.all true in
#check @returned_public_batch_preserves_actual_slot_invariant_order_and_frames
#print axioms returned_public_batch_preserves_actual_slot_invariant_order_and_frames
set_option pp.all true in
#check @returned_whole_walk_derives_global_order_invariant_unspent_and_frames
#print axioms returned_whole_walk_derives_global_order_invariant_unspent_and_frames
end ShielddSecurity.TransferCheckedWordWalk01
