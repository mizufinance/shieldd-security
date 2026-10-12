import ShielddSecurity.TransferGlobalCommitJoin01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBoundedNativeCodec01
open TransferStateDelta TransferIndexWriterModel01
open TransferNullifierBatchSource01 (Pending)
open TransferPendingFiniteCodec01 (NativePending restore erase)
open TransferPendingSetInvariant01 (Invariant Coherent)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request parentPending step walk allInputs)

/-! The native obligation covers only finite supported values: at most the
source consensus number of entries and canonical Jubjub Fq nullifier identities. Abstract
Nat values outside that domain are totalized in a separate ghost sum branch,
never asserted to be actual typed Rust objects. Successful bounded reachable
walks prove that every stored pending object stays in the native branch.
This supports reuse of the existing total source-model theorems without an
impossible obligation to encode every unbounded Nat as a native nullifier.
Actual nullifier-byte projection, NativePending typed embedding/Clone/finite
vector/set behavior, other-object embedding, all component finalization and
primitive/temporal/crypto/library/ownership/OS contracts remain explicit.
No ghost branch or hash identity gives runtime semantic/certification credit. -/

def nullifierModulus : Nat := 52435875175126190479447740508185965837690552500527637822603658699938581184513

def BoundedPending (pending : Pending) : Prop := ∀ key ∈ pending.ordered, key < nullifierModulus

def nativeSupported : NativePending → Bool
  | .opened ordered members => decide (ordered.length ≤ blockCapacity ∧ members.length ≤ blockCapacity) &&
      ordered.all (fun key => decide (key < nullifierModulus)) && members.all (fun key => decide (key < nullifierModulus))
  | .sealed ordered => decide (ordered.length ≤ blockCapacity) && ordered.all (fun key => decide (key < nullifierModulus))

def ExtendedObject (O : Type) := Sum O NativePending

def encodeObject {O : Type} (encodeNative : NativePending → O) (native : NativePending) : ExtendedObject O :=
  if nativeSupported native = true then .inl (encodeNative native) else .inr native

def decodeObject {O : Type} (decodeNative : O → NativePending) : ExtendedObject O → NativePending
  | .inl object => decodeNative object
  | .inr native => native

theorem bounded_consensus_pending_erases_to_supported_finite_native_domain
    (pending : Pending) (lengthBound : pending.ordered.length ≤ blockCapacity) (bounded : BoundedPending pending) :
    nativeSupported (erase pending) = true := by
  have bytes : pending.ordered.all (fun key => decide (key < nullifierModulus)) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact bounded
  cases sealed : pending.sealed <;> simp [erase, nativeSupported, sealed, lengthBound, bytes]

theorem restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts {O : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native) :
    ∀ native, restore (decodeObject decodeNative (encodeObject encodeNative native)) = restore native := by
  intro native
  by_cases supported : nativeSupported native = true
  · simp only [encodeObject, if_pos supported, decodeObject]
    exact supportedRoundtrip native supported
  · simp only [encodeObject, if_neg supported, decodeObject]

theorem supported_pending_encoding_is_actual_native_branch {O : Type}
    (encodeNative : NativePending → O) (pending : Pending)
    (lengthBound : pending.ordered.length ≤ blockCapacity) (bounded : BoundedPending pending) :
    TransferPendingFiniteCodec01.encode (encodeObject encodeNative) pending = .inl (encodeNative (erase pending)) := by
  simp only [TransferPendingFiniteCodec01.encode, encodeObject,
    if_pos (bounded_consensus_pending_erases_to_supported_finite_native_domain pending lengthBound bounded)]

theorem successful_bounded_whole_step_stores_supported_native_pending {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (request : Request (ExtendedObject O) E K X Tree A)
    (parent : State (ExtendedObject O)) (queued : List A) (committed : Commit (ExtendedObject O) E A)
    (initial : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent))
    (bounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent))
    (nativeInputs : ∀ key ∈ request.config.inputs request.action, key < nullifierModulus)
    (success : step (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project request parent queued = some committed) :
    Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project committed.parent) ∧
      BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project committed.parent) ∧
      committed.parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
        some (.inl (encodeNative (erase (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project committed.parent)))) := by
  have roundtrip := restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts encodeNative decodeNative supportedRoundtrip
  have coherentRoundtrip := TransferPendingFiniteCodec01.typed_finite_codec_restores_coherent_pending
    (encodeObject encodeNative) (decodeObject decodeNative) roundtrip
  obtain ⟨nextInvariant, ordered, stored⟩ := TransferReachablePendingBlock01.whole_step_preserves_reachable_pending_codec
    (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
    coherentRoundtrip project injection request parent queued committed initial success
  have nextBounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project committed.parent) := by
    intro key inside
    rw [ordered] at inside
    cases List.mem_append.mp inside with
    | inl earlier => exact bounded key earlier
    | inr current => exact nativeInputs key current
  refine ⟨nextInvariant, nextBounded, ?_⟩
  rw [stored, supported_pending_encoding_is_actual_native_branch encodeNative _ nextInvariant.2.2.1 nextBounded]

theorem successful_bounded_walk_never_stores_unsupported_pending_ghost {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (requests : List (Request (ExtendedObject O) E K X Tree A))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (initial : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent))
    (bounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent))
    (storedNative : ∃ object, parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (.inl object))
    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus)
    (success : walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final) :
    Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project final.1) ∧
      BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project final.1) ∧
      ∃ object, final.1.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (.inl object) := by
  induction requests generalizing parent queued with
  | nil =>
    have same : (parent, queued) = final := Option.some.inj success
    subst final
    exact ⟨initial, bounded, storedNative⟩
  | cons request rest ih =>
    cases first : step (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project request parent queued with
    | none => simp only [walk, first, Option.bind_none] at success; cases success
    | some committed =>
      have suffix : walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
          (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project committed.parent committed.deferred rest = some final := by
        simpa only [walk, first, Option.bind_some] using success
      obtain ⟨nextInvariant, nextBounded, stored⟩ := successful_bounded_whole_step_stores_supported_native_pending
        encodeNative decodeNative supportedRoundtrip project injection request parent queued committed initial bounded
        (nativeInputs request (by simp)) first
      exact ih committed.parent committed.deferred nextInvariant nextBounded ⟨_, stored⟩
        (fun later inside => nativeInputs later (List.mem_cons_of_mem request inside)) suffix

theorem bounded_whole_input_vector_from_native_action_projections {O E K X Tree A : Type}
    (requests : List (Request O E K X Tree A))
    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus) :
    ∀ key ∈ allInputs requests, key < nullifierModulus := by
  induction requests with
  | nil => intro key inside; cases inside
  | cons request rest ih =>
    intro key inside
    cases List.mem_append.mp inside with
    | inl current => exact nativeInputs request (by simp) key current
    | inr later => exact ih (fun item held => nativeInputs item (List.mem_cons_of_mem request held)) key later

theorem successful_bounded_default_walk_derives_supported_native_final_object {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (requests : List (Request (ExtendedObject O) E K X Tree A))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (storedDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (TransferPendingFiniteCodec01.encode (encodeObject encodeNative) TransferCurrentPendingReplay01.emptyPending))
    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus)
    (success : walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final) :
    Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project final.1) ∧
      BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project final.1) ∧
      ∃ object, final.1.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (.inl object) := by
  have emptyCoherent := (TransferPendingSetInvariant01.empty_pending_invariant blockCapacity).1
  have roundtrip := TransferPendingFiniteCodec01.typed_finite_codec_restores_coherent_pending
    (encodeObject encodeNative) (decodeObject decodeNative)
    (restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts encodeNative decodeNative supportedRoundtrip)
  have emptyRead : parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent = TransferCurrentPendingReplay01.emptyPending :=
    TransferReachablePendingBlock01.coherent_encoded_current_derives
      (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
      roundtrip _ ⟨parent, (empty : Cache (ExtendedObject O) Unit)⟩ TransferCurrentPendingReplay01.emptyPending emptyCoherent
      (by simpa only [apply_empty] using storedDefault)
  have emptyBounded : BoundedPending TransferCurrentPendingReplay01.emptyPending := by intro key inside; cases inside
  have initial : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent) := by
    rw [emptyRead]; exact TransferPendingSetInvariant01.empty_pending_invariant blockCapacity
  have bounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent) := by
    rw [emptyRead]; exact emptyBounded
  have storedNative : ∃ object, parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (.inl object) := by
    rw [storedDefault, supported_pending_encoding_is_actual_native_branch encodeNative TransferCurrentPendingReplay01.emptyPending (by decide) emptyBounded]
    exact ⟨_, rfl⟩
  exact successful_bounded_walk_never_stores_unsupported_pending_ghost encodeNative decodeNative supportedRoundtrip
    project injection requests parent queued final initial bounded storedNative nativeInputs success

theorem whole_bounded_default_publication_uses_only_supported_native_pending_and_exact_global_inputs {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (requests : List (Request (ExtendedObject O) E K X Tree A))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (storedDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (TransferPendingFiniteCodec01.encode (encodeObject encodeNative) TransferCurrentPendingReplay01.emptyPending))
    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus)
    (walked : walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final)
    (io : TransferEndToEnd01.Io (ExtendedObject O) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject O))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (projectedKeys : io.ending.project = project)
    (typedGetter : io.ending.decodePending = TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
    (finalization : TransferGlobalCommitJoin01.FinalizationPendingFrame io.ending
      (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project)
    (success : (TransferEndToEnd01.execute io host height final.2).root = some root) :
    (∃ object, final.1.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (.inl object)) ∧
    (∀ key ∈ allInputs requests, key < nullifierModulus) ∧
    ∃ frozen,
      frozen.insertions.accepted = allInputs requests ∧ (allInputs requests).Nodup ∧
      (allInputs requests).length ≤ blockCapacity ∧ frozen.next.applicationRoot = some root ∧
      (TransferEndToEnd01.execute io host height final.2).host.phase = .idle ∧
      (TransferEndToEnd01.execute io host height final.2).host.writer = .ready frozen.next ∧
      (TransferEndToEnd01.execute io host height final.2).host.store.ready = true ∧
      (TransferEndToEnd01.execute io host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
      (TransferEndToEnd01.execute io host height final.2).host.store.boundary = some frozen.next.nullifiers ∧
      frozen.next.nullifiers.roots.length = 16 ∧
      (TransferEndToEnd01.execute io host height final.2).host.store.healthy =
        (io.committing.writer.recoveryIo (TransferStatefulParticipantRecovery01.recoveryInput io.committing.writer
          (TransferEndToEnd01.sealed io host height final.2).host.store frozen)).healthyAfter := by
  have nativeFinal := successful_bounded_default_walk_derives_supported_native_final_object encodeNative decodeNative
    supportedRoundtrip project injection requests parent queued final storedDefault nativeInputs walked
  exact ⟨nativeFinal.2.2, bounded_whole_input_vector_from_native_action_projections requests nativeInputs,
    TransferGlobalCommitJoin01.whole_default_block_publication_commits_exact_global_inputs_under_finite_codec_and_finalization_field_contract
      (encodeObject encodeNative) (decodeObject decodeNative)
      (restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts encodeNative decodeNative supportedRoundtrip)
      project injection requests parent queued final storedDefault walked io host height root currentState projectedKeys typedGetter finalization success⟩

set_option pp.all true in
#check @nullifierModulus
#print axioms nullifierModulus
set_option pp.all true in
#check @BoundedPending
#print axioms BoundedPending
set_option pp.all true in
#check @nativeSupported
#print axioms nativeSupported
set_option pp.all true in
#check @ExtendedObject
#print axioms ExtendedObject
set_option pp.all true in
#check @encodeObject
#print axioms encodeObject
set_option pp.all true in
#check @decodeObject
#print axioms decodeObject
set_option pp.all true in
#check @bounded_consensus_pending_erases_to_supported_finite_native_domain
#print axioms bounded_consensus_pending_erases_to_supported_finite_native_domain
set_option pp.all true in
#check @restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts
#print axioms restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts
set_option pp.all true in
#check @supported_pending_encoding_is_actual_native_branch
#print axioms supported_pending_encoding_is_actual_native_branch
set_option pp.all true in
#check @successful_bounded_whole_step_stores_supported_native_pending
#print axioms successful_bounded_whole_step_stores_supported_native_pending
set_option pp.all true in
#check @successful_bounded_walk_never_stores_unsupported_pending_ghost
#print axioms successful_bounded_walk_never_stores_unsupported_pending_ghost
set_option pp.all true in
#check @bounded_whole_input_vector_from_native_action_projections
#print axioms bounded_whole_input_vector_from_native_action_projections
set_option pp.all true in
#check @successful_bounded_default_walk_derives_supported_native_final_object
#print axioms successful_bounded_default_walk_derives_supported_native_final_object
set_option pp.all true in
#check @whole_bounded_default_publication_uses_only_supported_native_pending_and_exact_global_inputs
#print axioms whole_bounded_default_publication_uses_only_supported_native_pending_and_exact_global_inputs
end ShielddSecurity.TransferBoundedNativeCodec01
