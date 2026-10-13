import ShielddSecurity.TransferWholeDurableReadback01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferNullifierConsensusLimits01
set_option autoImplicit false
open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01
open TransferVerificationEqualitySource01 (Item)
open TransferReadback (Store Boundary Status ReadGate MerkleContract)
open TransferNullifierBatchSource01 (Pending)
/-! Generated from the exact pinned Rust consensus capacity and qualified
whole-delivery contracts. Capacity is not a caller-selected model parameter.
Supported 32/64-bit usize representation is explicit; its native target and
Rust arithmetic correspondence remain an interface. The numeric capacity
inequality is derived in the kernel, not assumed. Native typed/reader/proof/
codec/Merkle/token/Host/durability interfaces are preserved unchanged. -/

def blockCapacity : Nat := 32768

def nativeWordMax (width : Nat) : Nat := 2 ^ width - 1
def SupportedWidth (width : Nat) : Prop := width = 32 ∨ width = 64

theorem capacity_below_supported_word (width : Nat) (supported : SupportedWidth width) :
    blockCapacity < nativeWordMax width := by
  rcases supported with rfl | rfl <;> decide

theorem whole_verified_unspent_at_consensus_capacity {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (decode : O → Store) (readerKey : Nat) (readBoundary : Delta O E → Option Boundary)
    (lockAvailable : Delta O E → Bool) (hash : String → Nat → List Nat)
    (verify : Nat → List Nat → Nat → Bool → Bool) (candidate : Delta O E → Nat → Option (Bool × Nat))
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (width : Nat) (supported : SupportedWidth width)
    (treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A) (committed : Commit O E A)
    (nonempty : (inputs action).isEmpty = false)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound (TransferWholeDurableReadback01.installReader raw decode readerKey readBoundary lockAvailable hash verify candidate)
        notes volume sct volumeAvailable extract inputs outputs (nativeWordMax width) blockCapacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item))
      registryMatches exclusive mode action parent queued = some committed) :
    ∀ key ∈ inputs action, ∃ (store : Store) (boundary : Boundary) (response : Status),
      TransferWholeDurableReadback01.currentReader decode readerKey ⟨parent, (empty : Cache O E)⟩ = some store ∧
      readBoundary ⟨parent, (empty : Cache O E)⟩ = some boundary ∧ lockAvailable ⟨parent, (empty : Cache O E)⟩ = true ∧
      TransferReadback.status hash verify store boundary key (candidate ⟨parent, (empty : Cache O E)⟩ key) = some response ∧ response.spent = false := by
  exact TransferWholeDurableReadback01.whole_success_every_input_verified_unspent api keys convert indexAvailable raw notes volume sct volumeAvailable
    decode readerKey readBoundary lockAvailable hash verify candidate extract inputs outputs
    (nativeWordMax width) blockCapacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item
    registryMatches exclusive mode parent queued committed nonempty (capacity_below_supported_word width supported) success
theorem whole_authenticated_absence_at_consensus_capacity {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (decode : O → Store) (readerKey : Nat) (readBoundary : Delta O E → Option Boundary)
    (lockAvailable : Delta O E → Bool) (hash : String → Nat → List Nat)
    (verify : Nat → List Nat → Nat → Bool → Bool) (candidate : Delta O E → Nat → Option (Bool × Nat))
    (leaves : Nat → List Nat → Option String) (merkle : MerkleContract verify leaves)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (width : Nat) (supported : SupportedWidth width)
    (treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A) (committed : Commit O E A)
    (nonempty : (inputs action).isEmpty = false)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound (TransferWholeDurableReadback01.installReader raw decode readerKey readBoundary lockAvailable hash verify candidate)
        notes volume sct volumeAvailable extract inputs outputs (nativeWordMax width) blockCapacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item))
      registryMatches exclusive mode action parent queued = some committed) :
    ∀ key ∈ inputs action, ∃ (store : Store) (boundary : Boundary) (response : Status),
      TransferWholeDurableReadback01.currentReader decode readerKey ⟨parent, (empty : Cache O E)⟩ = some store ∧
      readBoundary ⟨parent, (empty : Cache O E)⟩ = some boundary ∧ lockAvailable ⟨parent, (empty : Cache O E)⟩ = true ∧
      ReadGate store boundary (TransferReadback.key hash key) ∧ TransferReadback.partition (TransferReadback.key hash key) < 16 ∧
      response.nullifier = key ∧ response.boundary = boundary ∧ response.spent = false ∧
      verify (boundary.roots.getD (TransferReadback.partition (TransferReadback.key hash key)) 0)
        (TransferReadback.key hash key) response.proof false = true ∧
      leaves (boundary.roots.getD (TransferReadback.partition (TransferReadback.key hash key)) 0) (TransferReadback.key hash key) = none := by
  exact TransferWholeDurableReadback01.whole_success_every_input_authenticated_absence api keys convert indexAvailable raw notes volume sct volumeAvailable
    decode readerKey readBoundary lockAvailable hash verify candidate leaves merkle extract inputs outputs
    (nativeWordMax width) blockCapacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item
    registryMatches exclusive mode parent queued committed nonempty (capacity_below_supported_word width supported) success
theorem shared_input_replay_at_consensus_capacity {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (decode : O → Pending) (roundtrip : ∀ pending, decode (raw.nullifiers.encode pending) = pending)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (width : Nat) (supported : SupportedWidth width)
    (firstPayload firstEntry firstDay secondPayload secondEntry secondDay : Nat)
    (firstContext secondContext : TransferCapabilitySource01.ProofContext) (firstAction secondAction : A) (firstItem secondItem : Item)
    (firstRegistry firstExclusive secondRegistry secondExclusive : Bool) (firstMode secondMode : IndexMode)
    (parent : State O) (queued : List A) (firstCommit : Commit O E A) (shared : Nat)
    (firstMember : shared ∈ inputs firstAction) (secondMember : shared ∈ inputs secondAction)
    (firstSuccess : run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound (TransferCurrentPendingReplay01.withPending raw decode (project TransferNullifierObjectKeys01.nullifierBytes))
        notes volume sct volumeAvailable extract inputs outputs (nativeWordMax width) blockCapacity (project TransferNullifierObjectKeys01.treeBytes)
        (project TransferNullifierObjectKeys01.notesBytes) (project TransferNullifierObjectKeys01.volumeBytes) firstPayload
        (project TransferNullifierObjectKeys01.nullifierBytes) firstEntry firstDay firstContext firstAction firstItem))
      firstRegistry firstExclusive firstMode firstAction parent queued = some firstCommit) :
    let attempted := run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound (TransferCurrentPendingReplay01.withPending raw decode (project TransferNullifierObjectKeys01.nullifierBytes))
        notes volume sct volumeAvailable extract inputs outputs (nativeWordMax width) blockCapacity (project TransferNullifierObjectKeys01.treeBytes)
        (project TransferNullifierObjectKeys01.notesBytes) (project TransferNullifierObjectKeys01.volumeBytes) secondPayload
        (project TransferNullifierObjectKeys01.nullifierBytes) secondEntry secondDay secondContext secondAction secondItem))
      secondRegistry secondExclusive secondMode secondAction firstCommit.parent firstCommit.deferred
    attempted = none ∧ finish firstCommit.parent firstCommit.deferred attempted = (firstCommit.parent, firstCommit.deferred) := by
  exact TransferCurrentPendingReplay01.first_whole_success_then_shared_input_replay_preserves_first_parent_and_queue api keys convert indexAvailable raw notes volume sct volumeAvailable
    decode roundtrip extract inputs outputs project injection (nativeWordMax width) blockCapacity firstPayload firstEntry firstDay
    secondPayload secondEntry secondDay firstContext secondContext firstAction secondAction firstItem secondItem firstRegistry firstExclusive
    secondRegistry secondExclusive firstMode secondMode parent queued firstCommit shared firstMember secondMember
    (capacity_below_supported_word width supported) firstSuccess

set_option pp.all true in
#check @blockCapacity
#print axioms blockCapacity

set_option pp.all true in
#check @nativeWordMax
#print axioms nativeWordMax

set_option pp.all true in
#check @SupportedWidth
#print axioms SupportedWidth

set_option pp.all true in
#check @capacity_below_supported_word
#print axioms capacity_below_supported_word

set_option pp.all true in
#check @whole_verified_unspent_at_consensus_capacity
#print axioms whole_verified_unspent_at_consensus_capacity

set_option pp.all true in
#check @whole_authenticated_absence_at_consensus_capacity
#print axioms whole_authenticated_absence_at_consensus_capacity

set_option pp.all true in
#check @shared_input_replay_at_consensus_capacity
#print axioms shared_input_replay_at_consensus_capacity
end ShielddSecurity.TransferNullifierConsensusLimits01
