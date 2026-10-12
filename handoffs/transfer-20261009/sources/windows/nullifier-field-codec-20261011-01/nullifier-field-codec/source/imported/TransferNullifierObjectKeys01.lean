import ShielddSecurity.TransferPendingNullifierRetention01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferNullifierObjectKeys01
open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01
open TransferVerificationEqualitySource01 (Item)
/-! Generated only from exact pinned Rust static object-key literals and the
qualified whole retained-pending theorem. Byte inequality and an explicit
injective representation projection discharge all three key inequalities.
Hashing supplies source identity, not Rust semantics or cryptographic truth.
Native object/getter/codec/ownership/tree/reader/token/durability stay open. -/

def nullifierBytes : Bytes := [115, 99, 116, 47, 110, 117, 108, 108, 105, 102, 105, 101, 114, 115, 47, 112, 101, 110, 100, 105, 110, 103, 95, 98, 108, 111, 99, 107]

def treeBytes : Bytes := [115, 99, 116, 47, 99, 97, 99, 104, 101, 47, 99, 97, 99, 104, 101, 100, 95, 115, 116, 97, 116, 101, 95, 99, 111, 109, 109, 105, 116, 109, 101, 110, 116, 95, 116, 114, 101, 101]

def notesBytes : Bytes := [115, 104, 105, 101, 108, 100, 101, 100, 95, 112, 111, 111, 108, 47, 112, 101, 110, 100, 105, 110, 103, 95, 110, 111, 116, 101, 115]

def volumeBytes : Bytes := [115, 104, 105, 101, 108, 100, 101, 100, 95, 112, 111, 111, 108, 47, 112, 101, 110, 100, 105, 110, 103, 95, 118, 111, 108, 117, 109, 101, 95, 97, 99, 99, 117, 109, 117, 108, 97, 116, 111, 114, 95, 112, 97, 121, 108, 111, 97, 100, 115]

theorem source_key_bytes_separate :
    nullifierBytes ≠ treeBytes ∧ nullifierBytes ≠ notesBytes ∧ nullifierBytes ≠ volumeBytes := by decide

theorem projected_source_keys_separate (project : Bytes → Nat) (injection : Function.Injective project) :
    project nullifierBytes ≠ project treeBytes ∧ project nullifierBytes ≠ project notesBytes ∧
      project nullifierBytes ≠ project volumeBytes := by
  exact ⟨fun same => source_key_bytes_separate.1 (injection same),
    fun same => source_key_bytes_separate.2.1 (injection same),
    fun same => source_key_bytes_separate.2.2 (injection same)⟩

theorem whole_success_retains_source_key_pending_nullifier_encoding {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (wordMax capacity payload entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A) (committed : Commit O E A)
    (nonempty : (inputs action).isEmpty = false) (belowWord : capacity < wordMax)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity (project treeBytes) (project notesBytes)
        (project volumeBytes) payload (project nullifierBytes) entryKey dayKey context action item)) registryMatches exclusive mode action parent queued = some committed) :
    ∃ pending : TransferNullifierBatchSource01.Pending,
      TransferNullifierBatchSource01.inspect raw.nullifiers wordMax capacity ⟨parent, empty⟩ (inputs action) = .ok pending ∧
      committed.parent.objects (project nullifierBytes) = some (raw.nullifiers.encode pending) ∧
      pending.ordered = (raw.nullifiers.pending ⟨parent, empty⟩).ordered ++ inputs action ∧ pending.ordered.length ≤ capacity ∧
      pending.sealed = false ∧ ∀ key ∈ inputs action, raw.nullifiers.lookup ⟨parent, empty⟩ key = some false ∧
        (raw.nullifiers.pending ⟨parent, empty⟩).membership key = false ∧ pending.membership key = true := by
  have separate := projected_source_keys_separate project injection
  exact TransferPendingNullifierRetention01.whole_delivery_success_retains_bounded_fresh_pending_nullifier_encoding api keys convert indexAvailable
    raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity (project treeBytes) (project notesBytes) (project volumeBytes)
    payload (project nullifierBytes) entryKey dayKey context action item registryMatches exclusive mode parent queued committed nonempty belowWord
    separate.1 separate.2.1 separate.2.2 success

set_option pp.all true in
#check @nullifierBytes
#print axioms nullifierBytes

set_option pp.all true in
#check @treeBytes
#print axioms treeBytes

set_option pp.all true in
#check @notesBytes
#print axioms notesBytes

set_option pp.all true in
#check @volumeBytes
#print axioms volumeBytes

set_option pp.all true in
#check @source_key_bytes_separate
#print axioms source_key_bytes_separate

set_option pp.all true in
#check @projected_source_keys_separate
#print axioms projected_source_keys_separate

set_option pp.all true in
#check @whole_success_retains_source_key_pending_nullifier_encoding
#print axioms whole_success_retains_source_key_pending_nullifier_encoding
end ShielddSecurity.TransferNullifierObjectKeys01
