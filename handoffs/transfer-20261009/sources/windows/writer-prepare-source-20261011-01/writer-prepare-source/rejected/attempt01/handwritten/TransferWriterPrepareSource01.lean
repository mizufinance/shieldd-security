import ShielddSecurity.TransferReachablePendingBlock01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWriterPrepareSource01
open TransferStateDelta
open TransferPreparedAcceptedSource01 (Prepared)
open TransferNullifierBatchSource01 (Pending)
open TransferBlockPendingSequence01 (Request parentPending allInputs)

/-! PermanentWriter::prepare orders Ready/height/read lock, Store::prepare,
stage_boundary and Storage::prepare_commit before its single Prepared phase
assignment. Errors retain the original writer phase; disposable owned state
may have been staged. Preparation does not persist intent or commit a batch.
The stage/application callbacks are fallible source interfaces; root output
is independently observed. Native ownership, cloned boundary/Vec values,
fixed root/blockId types, prepared batch content, concurrency and actual
stage_boundary/storage implementation correspondence remain explicit. -/

structure CommitBoundary where
  nullifiers : TransferReadback.Boundary
  applicationRoot : Option Nat

structure Frozen where
  insertions : Prepared
  applicationRoot : Nat
  previous : CommitBoundary
  next : CommitBoundary

inductive Phase where
  | ready (boundary : CommitBoundary)
  | prepared (frozen : Frozen)
  | sealed (frozen : Frozen)
  | interrupted

structure Backend (O : Type) where
  height : State O → Option Nat
  readLock : Bool
  store : TransferPreparedAcceptedSource01.Backend
  stageBoundary : State O → Prepared → Option (State O)
  prepareApplication : State O → Option Nat

structure Outcome where
  phase : Phase
  returned : Option CommitBoundary

def prepareFrozen {O : Type} (backend : Backend O) (phase : Phase) (state : State O)
    (height : Fin (2 ^ 64)) (blockId accepted : List Nat) : Option Frozen :=
  match phase with
  | .ready previous =>
    backend.height state >>= fun actualHeight =>
      if actualHeight = height.val then
        if backend.readLock = true then
          TransferPreparedAcceptedSource01.prepare backend.store previous.nullifiers height blockId accepted >>= fun insertions =>
            backend.stageBoundary state insertions >>= fun staged =>
              backend.prepareApplication staged >>= fun root =>
                some ⟨insertions, root, previous, ⟨insertions.next, some root⟩⟩
        else none
      else none
  | _ => none

def prepareWriter {O : Type} (backend : Backend O) (phase : Phase) (state : State O)
    (height : Fin (2 ^ 64)) (blockId accepted : List Nat) : Outcome :=
  match prepareFrozen backend phase state height blockId accepted with
  | none => ⟨phase, none⟩
  | some frozen => ⟨.prepared frozen, some frozen.next⟩

theorem unready_refuses_before_height {O : Type} (backend : Backend O) (phase : Phase) (state : State O)
    (height : Fin (2 ^ 64)) (blockId accepted : List Nat) (unready : ∀ previous, phase ≠ .ready previous) :
    prepareFrozen backend phase state height blockId accepted = none := by
  cases phase with
  | ready previous => exact False.elim (unready previous rfl)
  | prepared _ => rfl
  | sealed _ => rfl
  | interrupted => rfl

theorem wrong_application_height_refuses_before_store {O : Type} (backend : Backend O) (previous : CommitBoundary) (state : State O)
    (height : Fin (2 ^ 64)) (blockId accepted : List Nat) (actualHeight : Nat)
    (read : backend.height state = some actualHeight) (different : actualHeight ≠ height.val) :
    prepareFrozen backend (.ready previous) state height blockId accepted = none := by
  simp only [prepareFrozen, read, Option.bind_some, if_neg different]

theorem successful_frozen_derives_every_prior_call {O : Type} (backend : Backend O) (phase : Phase) (state : State O)
    (height : Fin (2 ^ 64)) (blockId accepted : List Nat) (frozen : Frozen)
    (success : prepareFrozen backend phase state height blockId accepted = some frozen) :
    ∃ previous insertions staged root,
      phase = .ready previous ∧ backend.height state = some height.val ∧ backend.readLock = true ∧
      TransferPreparedAcceptedSource01.prepare backend.store previous.nullifiers height blockId accepted = some insertions ∧
      backend.stageBoundary state insertions = some staged ∧ backend.prepareApplication staged = some root ∧
      frozen = ⟨insertions, root, previous, ⟨insertions.next, some root⟩⟩ := by
  cases phase with
  | ready previous =>
    cases read : backend.height state with
    | none => simp only [prepareFrozen, read, Option.bind_none] at success; contradiction
    | some actual =>
      by_cases sameHeight : actual = height.val
      · by_cases locked : backend.readLock = true
        · cases stored : TransferPreparedAcceptedSource01.prepare backend.store previous.nullifiers height blockId accepted with
          | none => simp only [prepareFrozen, read, Option.bind_some, if_pos sameHeight, if_pos locked, stored, Option.bind_none] at success; contradiction
          | some insertions =>
            cases stage : backend.stageBoundary state insertions with
            | none => simp only [prepareFrozen, read, Option.bind_some, if_pos sameHeight, if_pos locked, stored, stage, Option.bind_none] at success; contradiction
            | some staged =>
              cases application : backend.prepareApplication staged with
              | none => simp only [prepareFrozen, read, Option.bind_some, if_pos sameHeight, if_pos locked, stored, stage, application, Option.bind_none] at success; contradiction
              | some root =>
                have exactFrozen : (⟨insertions, root, previous, ⟨insertions.next, some root⟩⟩ : Frozen) = frozen :=
                  Option.some.inj (by simpa only [prepareFrozen, read, Option.bind_some, if_pos sameHeight, if_pos locked, stored, stage, application] using success)
                exact ⟨previous, insertions, staged, root, rfl, congrArg some sameHeight, locked, rfl, rfl, rfl, exactFrozen.symm⟩
        · simp only [prepareFrozen, read, Option.bind_some, if_pos sameHeight, if_neg locked] at success; contradiction
      · simp only [prepareFrozen, read, Option.bind_some, if_neg sameHeight] at success; contradiction
  | prepared _ => simp only [prepareFrozen] at success; contradiction
  | sealed _ => simp only [prepareFrozen] at success; contradiction
  | interrupted => simp only [prepareFrozen] at success; contradiction

theorem failed_prepare_preserves_writer_phase {O : Type} (backend : Backend O) (phase : Phase) (state : State O)
    (height : Fin (2 ^ 64)) (blockId accepted : List Nat)
    (failed : prepareFrozen backend phase state height blockId accepted = none) :
    (prepareWriter backend phase state height blockId accepted).phase = phase ∧
      (prepareWriter backend phase state height blockId accepted).returned = none := by
  rw [prepareWriter, failed]
  exact ⟨rfl, rfl⟩

theorem successful_writer_derives_prepared_phase_exact_inputs_and_observed_root {O : Type}
    (backend : Backend O) (phase : Phase) (state : State O) (height : Fin (2 ^ 64)) (blockId accepted : List Nat)
    (returned : CommitBoundary) (success : (prepareWriter backend phase state height blockId accepted).returned = some returned) :
    ∃ frozen,
      prepareFrozen backend phase state height blockId accepted = some frozen ∧
      (prepareWriter backend phase state height blockId accepted).phase = .prepared frozen ∧
      returned = frozen.next ∧ frozen.insertions.accepted = accepted ∧
      returned.nullifiers = frozen.insertions.next ∧ returned.applicationRoot = some frozen.applicationRoot := by
  cases prepared : prepareFrozen backend phase state height blockId accepted with
  | none => simp only [prepareWriter, prepared] at success; contradiction
  | some frozen =>
    have returnedExact : frozen.next = returned := Option.some.inj (by simpa only [prepareWriter, prepared] using success)
    obtain ⟨previous, insertions, staged, root, _, _, _, stored, _, _, exactFrozen⟩ :=
      successful_frozen_derives_every_prior_call backend phase state height blockId accepted frozen prepared
    have inputs := (TransferPreparedAcceptedSource01.successful_prepare_derives_gate_and_exact_transition backend.store previous.nullifiers height blockId accepted insertions stored).2.2
    obtain ⟨observedRoots, _, _, _, _, _, acceptedExact⟩ := inputs
    refine ⟨frozen, rfl, ?_, returnedExact.symm, ?_, ?_, ?_⟩
    · simp only [prepareWriter, prepared]
    · rw [exactFrozen]; exact acceptedExact
    · rw [← returnedExact, exactFrozen]
    · rw [← returnedExact, exactFrozen]

theorem successful_block_writer_handoff_retains_exact_global_input_order {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending)
    (roundtrip : ∀ pending, TransferPendingSetInvariant01.Coherent pending → decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (emptyStart : parentPending decode project parent = TransferCurrentPendingReplay01.emptyPending)
    (walkSuccess : TransferBlockPendingSequence01.walk encode decode project parent queued requests = some final)
    (backend : Backend O) (phase : Phase) (height : Fin (2 ^ 64)) (blockId : List Nat) (returned : CommitBoundary)
    (success :
      let output := TransferPendingSealSource01.sealOnce encode decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨final.1, (empty : Cache O Unit)⟩
      let sealedState := applyCache final.1 output.cache
      (prepareWriter backend phase sealedState height blockId (parentPending decode project sealedState).ordered).returned = some returned) :
    let output := TransferPendingSealSource01.sealOnce encode decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨final.1, (empty : Cache O Unit)⟩
    let sealedState := applyCache final.1 output.cache
    ∃ frozen, (prepareWriter backend phase sealedState height blockId (parentPending decode project sealedState).ordered).phase = .prepared frozen ∧
      frozen.insertions.accepted = allInputs requests ∧ (allInputs requests).Nodup ∧
      (allInputs requests).length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
      returned.nullifiers = frozen.insertions.next ∧ returned.applicationRoot = some frozen.applicationRoot := by
  dsimp only at success ⊢
  have blockFacts := TransferReachablePendingBlock01.coherent_block_seals_exact_global_inputs_and_refuses_later_staging
    encode decode roundtrip project injection requests parent queued final emptyStart walkSuccess
  obtain ⟨frozen, _, preparedPhase, _, exactInputs, next, root⟩ :=
    successful_writer_derives_prepared_phase_exact_inputs_and_observed_root backend phase _ height blockId _ returned success
  exact ⟨frozen, preparedPhase, exactInputs.trans blockFacts.2.2.2.2.1,
    blockFacts.2.2.2.2.2.1, blockFacts.2.2.2.2.2.2.1, next, root⟩

theorem finite_codec_default_writer_handoff_retains_exact_global_inputs {O E K X Tree A : Type}
    (encodeNative : TransferPendingFiniteCodec01.NativePending → O) (decodeNative : O → TransferPendingFiniteCodec01.NativePending)
    (typedRoundtrip : ∀ native, TransferPendingFiniteCodec01.restore (decodeNative (encodeNative native)) = TransferPendingFiniteCodec01.restore native)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (storedDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (TransferPendingFiniteCodec01.encode encodeNative TransferCurrentPendingReplay01.emptyPending))
    (walkSuccess : TransferBlockPendingSequence01.walk (TransferPendingFiniteCodec01.encode encodeNative)
      (TransferPendingFiniteCodec01.decode decodeNative) project parent queued requests = some final)
    (backend : Backend O) (phase : Phase) (height : Fin (2 ^ 64)) (blockId : List Nat) (returned : CommitBoundary)
    (success :
      let output := TransferPendingSealSource01.sealOnce (TransferPendingFiniteCodec01.encode encodeNative)
        (TransferPendingFiniteCodec01.decode decodeNative) (project TransferNullifierObjectKeys01.nullifierBytes) ⟨final.1, (empty : Cache O Unit)⟩
      let sealedState := applyCache final.1 output.cache
      (prepareWriter backend phase sealedState height blockId (parentPending (TransferPendingFiniteCodec01.decode decodeNative) project sealedState).ordered).returned = some returned) :
    let output := TransferPendingSealSource01.sealOnce (TransferPendingFiniteCodec01.encode encodeNative)
      (TransferPendingFiniteCodec01.decode decodeNative) (project TransferNullifierObjectKeys01.nullifierBytes) ⟨final.1, (empty : Cache O Unit)⟩
    let sealedState := applyCache final.1 output.cache
    ∃ frozen, (prepareWriter backend phase sealedState height blockId (parentPending (TransferPendingFiniteCodec01.decode decodeNative) project sealedState).ordered).phase = .prepared frozen ∧
      frozen.insertions.accepted = allInputs requests ∧ (allInputs requests).Nodup ∧
      (allInputs requests).length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
      returned.nullifiers = frozen.insertions.next ∧ returned.applicationRoot = some frozen.applicationRoot := by
  have reachableRoundtrip : ∀ pending, TransferPendingSetInvariant01.Coherent pending →
      TransferPendingFiniteCodec01.decode decodeNative (TransferPendingFiniteCodec01.encode encodeNative pending) = pending :=
    TransferPendingFiniteCodec01.typed_finite_codec_restores_coherent_pending encodeNative decodeNative typedRoundtrip
  have emptyCoherent : TransferPendingSetInvariant01.Coherent TransferCurrentPendingReplay01.emptyPending :=
    (TransferPendingSetInvariant01.empty_pending_invariant TransferNullifierConsensusLimits01.blockCapacity).1
  have emptyStart : parentPending (TransferPendingFiniteCodec01.decode decodeNative) project parent = TransferCurrentPendingReplay01.emptyPending :=
    TransferReachablePendingBlock01.coherent_encoded_current_derives (TransferPendingFiniteCodec01.encode encodeNative)
      (TransferPendingFiniteCodec01.decode decodeNative) reachableRoundtrip _ ⟨parent, (empty : Cache O Unit)⟩
      TransferCurrentPendingReplay01.emptyPending emptyCoherent (by simpa only [apply_empty] using storedDefault)
  exact successful_block_writer_handoff_retains_exact_global_input_order (TransferPendingFiniteCodec01.encode encodeNative)
    (TransferPendingFiniteCodec01.decode decodeNative) reachableRoundtrip project injection requests parent queued final emptyStart walkSuccess
    backend phase height blockId returned success

set_option pp.all true in
#check @CommitBoundary
#print axioms CommitBoundary
set_option pp.all true in
#check @Frozen
#print axioms Frozen
set_option pp.all true in
#check @Phase
#print axioms Phase
set_option pp.all true in
#check @Backend
#print axioms Backend
set_option pp.all true in
#check @Outcome
#print axioms Outcome
set_option pp.all true in
#check @prepareFrozen
#print axioms prepareFrozen
set_option pp.all true in
#check @prepareWriter
#print axioms prepareWriter
set_option pp.all true in
#check @unready_refuses_before_height
#print axioms unready_refuses_before_height
set_option pp.all true in
#check @wrong_application_height_refuses_before_store
#print axioms wrong_application_height_refuses_before_store
set_option pp.all true in
#check @successful_frozen_derives_every_prior_call
#print axioms successful_frozen_derives_every_prior_call
set_option pp.all true in
#check @failed_prepare_preserves_writer_phase
#print axioms failed_prepare_preserves_writer_phase
set_option pp.all true in
#check @successful_writer_derives_prepared_phase_exact_inputs_and_observed_root
#print axioms successful_writer_derives_prepared_phase_exact_inputs_and_observed_root
set_option pp.all true in
#check @successful_block_writer_handoff_retains_exact_global_input_order
#print axioms successful_block_writer_handoff_retains_exact_global_input_order
set_option pp.all true in
#check @finite_codec_default_writer_handoff_retains_exact_global_inputs
#print axioms finite_codec_default_writer_handoff_retains_exact_global_inputs
end ShielddSecurity.TransferWriterPrepareSource01
