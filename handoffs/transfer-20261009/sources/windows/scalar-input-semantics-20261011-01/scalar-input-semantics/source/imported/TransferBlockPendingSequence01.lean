import ShielddSecurity.TransferPendingSetInvariant01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlockPendingSequence01
open TransferStateDelta TransferIndexWriterModel01
open TransferVerificationEqualitySource01 (Item)
open TransferNullifierBatchSource01 (Pending)
open TransferWholeReaderRefusal01 (Config)
open TransferPendingSetInvariant01 (Invariant)
open TransferNullifierConsensusLimits01 (SupportedWidth blockCapacity nativeWordMax)

/-! Symbolic sequential composition of actual whole-delivery model calls.
Each request installs the current pending getter and fixed typed encoding at
source-derived static keys, with source consensus capacity. Requests retain
explicit supported word width and nonempty input projections; complete-Item
reextraction, nullifier admission, notes, ordinary volume and mode/index
success are derived from full run success. Starting object absence derives
the empty invariant. No desired per-step invariant or successful callback is
supplied to the walk theorem. Typed encoding/Clone/getter/collections, native
proof/reader/hash/codec/boundary/ownership/crypto remain interfaces. This walk
projects state and deferred queue and does not model event publication, Host
finalization, durability or block rollback. No native/control/certification
credit. Finite reusable list induction; no unrolled wide walk. -/

def parentPending {O : Type} (decode : O → Pending) (project : Bytes → Nat) (parent : State O) : Pending :=
  TransferCurrentPendingReplay01.currentPending decode (project TransferNullifierObjectKeys01.nullifierBytes)
    ⟨parent, (empty : Cache O Unit)⟩

def bindPending {O E K X Tree A : Type} (config : Config O E K X Tree A)
    (encode : Pending → O) (decode : O → Pending) (project : Bytes → Nat) : Config O E K X Tree A :=
  {config with
    raw := TransferCurrentPendingReplay01.withPending
      {config.raw with nullifiers := {config.raw.nullifiers with encode := encode}}
      decode (project TransferNullifierObjectKeys01.nullifierBytes)
    treeKey := project TransferNullifierObjectKeys01.treeBytes
    notesKey := project TransferNullifierObjectKeys01.notesBytes
    volumeKey := project TransferNullifierObjectKeys01.volumeBytes
    nullifierKey := project TransferNullifierObjectKeys01.nullifierBytes}

structure Request (O E K X Tree A : Type) where
  config : Config O E K X Tree A
  context : TransferCapabilitySource01.ProofContext
  action : A
  item : Item
  registryMatches : Bool
  exclusive : Bool
  mode : IndexMode
  supported : SupportedWidth config.width
  nonempty : (config.inputs action).isEmpty = false

def step {O E K X Tree A : Type} (encode : Pending → O) (decode : O → Pending) (project : Bytes → Nat)
    (request : Request O E K X Tree A) (parent : State O) (queued : List A) : Option (Commit O E A) :=
  run (TransferWholeReaderRefusal01.delivery (bindPending request.config encode decode project) request.context request.action request.item)
    request.registryMatches request.exclusive request.mode request.action parent queued

def walk {O E K X Tree A : Type} (encode : Pending → O) (decode : O → Pending) (project : Bytes → Nat)
    (parent : State O) (queued : List A) : List (Request O E K X Tree A) → Option (State O × List A)
  | [] => some (parent, queued)
  | request :: rest => (step encode decode project request parent queued).bind fun committed =>
      walk encode decode project committed.parent committed.deferred rest

def allInputs {O E K X Tree A : Type} : List (Request O E K X Tree A) → List Nat
  | [] => []
  | request :: rest => request.config.inputs request.action ++ allInputs rest

theorem absent_parent_derives_empty_invariant {O : Type} (decode : O → Pending) (project : Bytes → Nat) (parent : State O)
    (absent : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) = none) :
    Invariant blockCapacity (parentPending decode project parent) := by
  have emptyRead : parentPending decode project parent = TransferCurrentPendingReplay01.emptyPending := by
    exact TransferCurrentPendingReplay01.current_object_absence_derives_default decode _ ⟨parent, (empty : Cache O Unit)⟩
      (by simpa only [apply_empty] using absent)
  rw [emptyRead]
  exact TransferPendingSetInvariant01.empty_pending_invariant blockCapacity

theorem whole_step_preserves_pending_invariant {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (request : Request O E K X Tree A)
    (parent : State O) (queued : List A) (committed : Commit O E A)
    (initial : Invariant blockCapacity (parentPending decode project parent))
    (success : step encode decode project request parent queued = some committed) :
    Invariant blockCapacity (parentPending decode project committed.parent) ∧
      (parentPending decode project committed.parent).ordered = (parentPending decode project parent).ordered ++ request.config.inputs request.action ∧
      committed.parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (encode (parentPending decode project committed.parent)) := by
  let config := request.config
  let raw := TransferWholeDurableReadback01.installReader
    (bindPending config encode decode project).raw config.decode config.readerKey config.readBoundary config.lockAvailable config.hash config.verify config.candidate
  obtain ⟨pending, inspected, stored, ordered, _, _, _⟩ :=
    TransferNullifierObjectKeys01.whole_success_retains_source_key_pending_nullifier_encoding config.api config.keys config.convert config.indexAvailable
      raw config.notes config.volume config.sct config.volumeAvailable config.extract config.inputs config.outputs project injection
      (nativeWordMax config.width) blockCapacity config.payload config.entryKey config.dayKey request.context request.action request.item
      request.registryMatches request.exclusive request.mode parent queued committed request.nonempty
      (TransferNullifierConsensusLimits01.capacity_below_supported_word config.width request.supported) success
  have previous : raw.nullifiers.pending ⟨parent, (empty : Cache O E)⟩ = parentPending decode project parent := by
    change TransferCurrentPendingReplay01.currentPending decode (project TransferNullifierObjectKeys01.nullifierBytes)
      ⟨parent, (empty : Cache O E)⟩ = parentPending decode project parent
    simp only [TransferCurrentPendingReplay01.currentPending, parentPending, apply_empty]
  have coherent : TransferPendingSetInvariant01.Coherent (raw.nullifiers.pending ⟨parent, (empty : Cache O E)⟩) := by
    rw [previous]
    exact initial.1
  have nodup : (raw.nullifiers.pending ⟨parent, (empty : Cache O E)⟩).ordered.Nodup := by
    rw [previous]
    exact initial.2.1
  have invariant := TransferPendingSetInvariant01.successful_inspection_preserves_invariant raw.nullifiers (nativeWordMax config.width)
    blockCapacity ⟨parent, (empty : Cache O E)⟩ (config.inputs request.action) pending coherent nodup
    (TransferNullifierConsensusLimits01.capacity_below_supported_word config.width request.supported) inspected
  have after : parentPending decode project committed.parent = pending := by
    exact TransferCurrentPendingReplay01.encoded_current_object_derives_pending encode decode roundtrip _
      ⟨committed.parent, (empty : Cache O Unit)⟩ pending (by simpa only [apply_empty] using stored)
  rw [previous] at ordered
  rw [after]
  exact ⟨invariant, ordered, stored⟩

theorem successful_walk_preserves_invariant_and_exact_input_order {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (initial : Invariant blockCapacity (parentPending decode project parent))
    (success : walk encode decode project parent queued requests = some final) :
    Invariant blockCapacity (parentPending decode project final.1) ∧
      (parentPending decode project final.1).ordered = (parentPending decode project parent).ordered ++ allInputs requests := by
  induction requests generalizing parent queued with
  | nil =>
    have same : (parent, queued) = final := Option.some.inj success
    subst final
    exact ⟨initial, by simp only [allInputs, List.append_nil]⟩
  | cons request rest ih =>
    cases first : step encode decode project request parent queued with
    | none => simp only [walk, first, Option.bind_none] at success; contradiction
    | some committed =>
      have later : walk encode decode project committed.parent committed.deferred rest = some final := by
        simpa only [walk, first, Option.bind_some] using success
      obtain ⟨nextInvariant, nextOrdered, _⟩ := whole_step_preserves_pending_invariant encode decode roundtrip project injection request
        parent queued committed initial first
      obtain ⟨finalInvariant, finalOrdered⟩ := ih committed.parent committed.deferred nextInvariant later
      refine ⟨finalInvariant, ?_⟩
      rw [finalOrdered, nextOrdered]
      exact List.append_assoc _ _ _

theorem absent_start_successful_block_derives_global_distinct_bounded_membership {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (absent : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) = none)
    (success : walk encode decode project parent queued requests = some final) :
    Invariant blockCapacity (parentPending decode project final.1) ∧
      (parentPending decode project final.1).ordered = allInputs requests ∧ (allInputs requests).Nodup ∧
      (allInputs requests).length ≤ blockCapacity ∧
      ∀ key, (parentPending decode project final.1).membership key = (allInputs requests).contains key := by
  have initial := absent_parent_derives_empty_invariant decode project parent absent
  obtain ⟨invariant, ordered⟩ := successful_walk_preserves_invariant_and_exact_input_order encode decode roundtrip project injection
    requests parent queued final initial success
  have emptyRead : parentPending decode project parent = TransferCurrentPendingReplay01.emptyPending := by
    exact TransferCurrentPendingReplay01.current_object_absence_derives_default decode _ ⟨parent, (empty : Cache O Unit)⟩
      (by simpa only [apply_empty] using absent)
  have exactOrder : (parentPending decode project final.1).ordered = allInputs requests := by
    simpa only [emptyRead, TransferCurrentPendingReplay01.emptyPending, List.nil_append] using ordered
  refine ⟨invariant, exactOrder, ?_, ?_, ?_⟩
  · rw [← exactOrder]
    exact invariant.2.1
  · rw [← exactOrder]
    exact invariant.2.2.1
  · intro key
    rw [invariant.1 key, exactOrder]

set_option pp.all true in
#check @parentPending
#print axioms parentPending
set_option pp.all true in
#check @bindPending
#print axioms bindPending
set_option pp.all true in
#check @Request
#print axioms Request
set_option pp.all true in
#check @step
#print axioms step
set_option pp.all true in
#check @walk
#print axioms walk
set_option pp.all true in
#check @allInputs
#print axioms allInputs
set_option pp.all true in
#check @absent_parent_derives_empty_invariant
#print axioms absent_parent_derives_empty_invariant
set_option pp.all true in
#check @whole_step_preserves_pending_invariant
#print axioms whole_step_preserves_pending_invariant
set_option pp.all true in
#check @successful_walk_preserves_invariant_and_exact_input_order
#print axioms successful_walk_preserves_invariant_and_exact_input_order
set_option pp.all true in
#check @absent_start_successful_block_derives_global_distinct_bounded_membership
#print axioms absent_start_successful_block_derives_global_distinct_bounded_membership
end ShielddSecurity.TransferBlockPendingSequence01
