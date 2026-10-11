import ShielddSecurity.TransferPendingSealSource01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlockSealJoin01
open TransferStateDelta
open TransferNullifierBatchSource01 (Pending)
open TransferBlockPendingSequence01 (Request parentPending allInputs)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferPendingSetInvariant01 (Invariant)
open TransferPendingSealSource01 (sealOnce freeze ensureSealed SealError)

/-! Join the same successful whole-delivery block walk to one-shot sealing.
Nonempty successful walks retain an encoded Open object, so ensure-sealed
refuses before sealing. Every successful walk from an empty default read
seals its exact accumulated input order, with globally distinct/bounded frozen
membership and derived repeated-seal/later-whole-stage refusal. State V/NV
domains and empty seal events are preserved. Typed representation and actual
native request/phase scheduling/getter/Clone/enum/owner interfaces remain
explicit. Host end_block calls application end_block before reading pending
ordered values into writer.prepare; no later owner mutation, NOMT commit,
event publication, crash durability or native control is certified here. -/

theorem encoded_default_start_derives_empty_read {O : Type} (encode : Pending → O) (decode : O → Pending)
    (roundtrip : ∀ pending, decode (encode pending) = pending) (project : Bytes → Nat) (parent : State O)
    (stored : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (encode TransferCurrentPendingReplay01.emptyPending)) :
    parentPending decode project parent = TransferCurrentPendingReplay01.emptyPending := by
  exact TransferCurrentPendingReplay01.encoded_current_object_derives_pending encode decode roundtrip _ ⟨parent, (empty : Cache O Unit)⟩
    TransferCurrentPendingReplay01.emptyPending (by simpa only [apply_empty] using stored)

theorem empty_start_successful_walk_derives_global_inputs {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (emptyStart : parentPending decode project parent = TransferCurrentPendingReplay01.emptyPending)
    (success : TransferBlockPendingSequence01.walk encode decode project parent queued requests = some final) :
    Invariant blockCapacity (parentPending decode project final.1) ∧
      (parentPending decode project final.1).ordered = allInputs requests ∧ (allInputs requests).Nodup ∧
      (allInputs requests).length ≤ blockCapacity ∧
      ∀ key, (parentPending decode project final.1).membership key = (allInputs requests).contains key := by
  have initial : Invariant blockCapacity (parentPending decode project parent) := by
    rw [emptyStart]
    exact TransferPendingSetInvariant01.empty_pending_invariant blockCapacity
  obtain ⟨invariant, ordered⟩ := TransferBlockPendingSequence01.successful_walk_preserves_invariant_and_exact_input_order encode decode roundtrip
    project injection requests parent queued final initial success
  have exactOrder : (parentPending decode project final.1).ordered = allInputs requests := by
    simpa only [emptyStart, TransferCurrentPendingReplay01.emptyPending, List.nil_append] using ordered
  refine ⟨invariant, exactOrder, ?_, ?_, ?_⟩
  · rw [← exactOrder]
    exact invariant.2.1
  · rw [← exactOrder]
    exact invariant.2.2.1
  · intro key
    rw [invariant.1 key, exactOrder]

theorem nonempty_successful_walk_retains_current_encoding {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A) (nonempty : requests ≠ [])
    (initial : Invariant blockCapacity (parentPending decode project parent))
    (success : TransferBlockPendingSequence01.walk encode decode project parent queued requests = some final) :
    final.1.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (encode (parentPending decode project final.1)) := by
  induction requests generalizing parent queued with
  | nil => exact False.elim (nonempty rfl)
  | cons request rest ih =>
    cases first : TransferBlockPendingSequence01.step encode decode project request parent queued with
    | none => simp only [TransferBlockPendingSequence01.walk, first, Option.bind_none] at success; contradiction
    | some committed =>
      have later : TransferBlockPendingSequence01.walk encode decode project committed.parent committed.deferred rest = some final := by
        simpa only [TransferBlockPendingSequence01.walk, first, Option.bind_some] using success
      obtain ⟨nextInvariant, _, stored⟩ := TransferBlockPendingSequence01.whole_step_preserves_pending_invariant encode decode roundtrip project injection
        request parent queued committed initial first
      cases rest with
      | nil =>
        have same : (committed.parent, committed.deferred) = final := Option.some.inj later
        subst final
        exact stored
      | cons next remaining =>
        exact ih committed.parent committed.deferred (by intro impossible; contradiction) nextInvariant later

theorem nonempty_successful_open_block_refuses_finalization_gate {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A) (nonempty : requests ≠ [])
    (emptyStart : parentPending decode project parent = TransferCurrentPendingReplay01.emptyPending)
    (success : TransferBlockPendingSequence01.walk encode decode project parent queued requests = some final) :
    ensureSealed decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨final.1, (empty : Cache O Unit)⟩ = .error .notSealed := by
  have initial : Invariant blockCapacity (parentPending decode project parent) := by
    rw [emptyStart]
    exact TransferPendingSetInvariant01.empty_pending_invariant blockCapacity
  have stored := nonempty_successful_walk_retains_current_encoding encode decode roundtrip project injection requests parent queued final nonempty initial success
  have invariant := (TransferBlockPendingSequence01.successful_walk_preserves_invariant_and_exact_input_order encode decode roundtrip project injection
    requests parent queued final initial success).1
  exact TransferPendingSealSource01.encoded_open_ensure_refuses encode decode roundtrip _ ⟨final.1, empty⟩ (parentPending decode project final.1)
    (by simpa only [apply_empty] using stored) invariant.2.2.2

theorem successful_block_seals_exact_global_inputs_once_and_refuses_later_staging {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (emptyStart : parentPending decode project parent = TransferCurrentPendingReplay01.emptyPending)
    (success : TransferBlockPendingSequence01.walk encode decode project parent queued requests = some final) :
    let output := sealOnce encode decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨final.1, (empty : Cache O Unit)⟩
    let sealedState := applyCache final.1 output.cache
    output.result = .ok () ∧ sealedState.verifiable = final.1.verifiable ∧ sealedState.nonverifiable = final.1.nonverifiable ∧
      output.cache.events = [] ∧ (parentPending decode project sealedState).ordered = allInputs requests ∧
      (allInputs requests).Nodup ∧ (allInputs requests).length ≤ blockCapacity ∧
      (∀ key, (parentPending decode project sealedState).membership key = (allInputs requests).contains key) ∧
      (parentPending decode project sealedState).sealed = true ∧
      ensureSealed decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨sealedState, (empty : Cache O Unit)⟩ = .ok () ∧
      sealOnce encode decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨sealedState, (empty : Cache O Unit)⟩ =
        ⟨(empty : Cache O Unit), .error .alreadySealed⟩ ∧
      ∀ later : Request O E K X Tree A,
        let attempted := TransferBlockPendingSequence01.step encode decode project later sealedState final.2
        attempted = none ∧ finish sealedState final.2 attempted = (sealedState, final.2) := by
  dsimp only
  have blockFacts := empty_start_successful_walk_derives_global_inputs encode decode roundtrip
    project injection requests parent queued final emptyStart success
  let child : Delta O Unit := ⟨final.1, empty⟩
  let output := sealOnce encode decode (project TransferNullifierObjectKeys01.nullifierBytes) child
  let sealedState := applyCache final.1 output.cache
  have opened : (TransferCurrentPendingReplay01.currentPending decode (project TransferNullifierObjectKeys01.nullifierBytes) child).sealed = false :=
    blockFacts.1.2.2.2
  have frames := TransferPendingSealSource01.opened_seal_derives_single_object_and_frames encode decode _ child opened
  have stored : sealedState.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (encode (freeze (parentPending decode project final.1))) :=
    frames.2.2.2.2.2
  have frozenRead : parentPending decode project sealedState = freeze (parentPending decode project final.1) := by
    exact TransferCurrentPendingReplay01.encoded_current_object_derives_pending encode decode roundtrip _
      ⟨sealedState, (empty : Cache O Unit)⟩ (freeze (parentPending decode project final.1)) (by simpa only [apply_empty] using stored)
  have sealed : (parentPending decode project sealedState).sealed = true := by rw [frozenRead]; rfl
  refine ⟨frames.1, ?_, ?_, frames.2.2.2.1, ?_, blockFacts.2.2.1, blockFacts.2.2.2.1, ?_, sealed, ?_, ?_, ?_⟩
  · change overlay final.1.verifiable output.cache.verifiable = final.1.verifiable
    rw [frames.2.1]
    rfl
  · change overlay final.1.nonverifiable output.cache.nonverifiable = final.1.nonverifiable
    rw [frames.2.2.1]
    rfl
  · rw [frozenRead]
    exact blockFacts.2.1
  · intro key
    rw [frozenRead]
    change (parentPending decode project final.1).ordered.contains key = (allInputs requests).contains key
    rw [blockFacts.2.1]
  · exact TransferPendingSealSource01.encoded_frozen_ensure_succeeds encode decode roundtrip _ ⟨sealedState, (empty : Cache O Unit)⟩
      (parentPending decode project final.1) (by simpa only [apply_empty] using stored)
  · exact TransferPendingSealSource01.already_sealed_error_retains_input_cache encode decode _ ⟨sealedState, (empty : Cache O Unit)⟩ sealed
  · intro later
    exact TransferPendingSealSource01.whole_request_after_current_sealing_preserves_parent_and_queue encode decode project injection later sealedState final.2 sealed

set_option pp.all true in
#check @encoded_default_start_derives_empty_read
#print axioms encoded_default_start_derives_empty_read
set_option pp.all true in
#check @empty_start_successful_walk_derives_global_inputs
#print axioms empty_start_successful_walk_derives_global_inputs
set_option pp.all true in
#check @nonempty_successful_walk_retains_current_encoding
#print axioms nonempty_successful_walk_retains_current_encoding
set_option pp.all true in
#check @nonempty_successful_open_block_refuses_finalization_gate
#print axioms nonempty_successful_open_block_refuses_finalization_gate
set_option pp.all true in
#check @successful_block_seals_exact_global_inputs_once_and_refuses_later_staging
#print axioms successful_block_seals_exact_global_inputs_once_and_refuses_later_staging
end ShielddSecurity.TransferBlockSealJoin01
