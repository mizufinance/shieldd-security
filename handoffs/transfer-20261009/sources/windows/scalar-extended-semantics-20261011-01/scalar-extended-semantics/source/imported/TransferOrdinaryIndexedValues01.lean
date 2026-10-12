import ShielddSecurity.TransferOrdinaryIndexDelivery01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferOrdinaryIndexedValues01

open TransferStateDelta TransferRawStateProgram01
open TransferIndexWriterModel01 (Codec Backend)
open TransferVerificationEqualitySource01 (Item)

/-! The same action argument is used by the stateless extractor, raw input/
output projections, transaction conversion and transaction index. Byte-key
projection injectivity is a representation interface, not a hash assumption.
Whole success derives visible V markers and the three exact NV index values;
all other NV keys preserve the original parent. This is functional child
application, with all inherited Rust/proof/store/durability interfaces open. -/

theorem same_action_success_derives_visible_index_and_volume_values {O E K X Tree A : Type}
    (api : Api O E A) (project : Bytes → Nat) (injection : Function.Injective project)
    (prefixBytes : Nat → Bytes) (ordinalBytes : Nat → Bytes) (codec : Codec) (index : Backend O E A)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (registryMatches exclusive : Bool) (parent : State O)
    (queued : List A) (committed : Commit O E A) (different : entryKey ≠ dayKey)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api
      (TransferIndexInspectionFacts01.keysFromBytes project prefixBytes ordinalBytes) codec index
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct available extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item))
      registryMatches exclusive .perTransaction action parent queued = some committed) :
    let keys := TransferIndexInspectionFacts01.keysFromBytes project prefixBytes ordinalBytes
    ∃ (height : Nat) (witness : TransferIndexWriterModel01.Witness),
      extract action .ordinary = .ok item ∧ index.convert action = some witness.encoded ∧
      witness.next.val = witness.ordinal.val + 1 ∧ witness.ordinal.val + 1 < 2 ^ 64 ∧
      parent.verifiable entryKey = none ∧
      committed.parent.verifiable entryKey = some [1] ∧ committed.parent.verifiable dayKey = some [1] ∧
      committed.parent.nonverifiable (keys.entry height witness.ordinal.val) = some witness.encoded.payload ∧
      committed.parent.nonverifiable (keys.identifier height witness.encoded.identifier) = some (codec.encodeCount witness.ordinal) ∧
      committed.parent.nonverifiable (keys.count height) = some (codec.encodeCount witness.next) ∧
      committed.deferred = queued := by
  obtain ⟨reextracted, fresh, volumeEntry, volumeDay, deferred⟩ :=
    TransferOrdinaryIndexDelivery01.bound_ordinary_per_transaction_success_derives_markers api
      (TransferIndexInspectionFacts01.keysFromBytes project prefixBytes ordinalBytes) codec index raw notes volume sct available
      extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey
      action item registryMatches exclusive action parent queued committed different success
  obtain ⟨height, witness, _, converted, _, _, _, increment, bound, applied⟩ :=
    TransferOrdinaryIndexDelivery01.per_transaction_success_derives_checked_index_observations api
      (TransferIndexInspectionFacts01.keysFromBytes project prefixBytes ordinalBytes) codec index
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct available extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item)
      registryMatches exclusive action parent queued committed success
  obtain ⟨entryCount, idCount, entryId⟩ := TransferIndexInspectionFacts01.projected_keys_separate
    project injection prefixBytes ordinalBytes height witness.ordinal.val witness.encoded.identifier
  refine ⟨height, witness, reextracted, converted, increment, bound, fresh, volumeEntry, volumeDay, ?_, ?_, ?_, deferred⟩
  · rw [applied]
    simp only [applyCache, overlay, TransferIndexInspectionFacts01.writeIndex_entry _ codec height witness _ entryCount entryId]
  · rw [applied]
    simp only [applyCache, overlay, TransferIndexInspectionFacts01.writeIndex_identifier _ codec height witness _ idCount]
  · rw [applied]
    simp only [applyCache, overlay, TransferIndexWriterModel01.writeIndex_count]

theorem same_action_success_preserves_every_other_nonverifiable_key {O E K X Tree A : Type}
    (api : Api O E A) (project : Bytes → Nat) (prefixBytes : Nat → Bytes) (ordinalBytes : Nat → Bytes)
    (codec : Codec) (index : Backend O E A)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (registryMatches exclusive : Bool) (parent : State O)
    (queued : List A) (committed : Commit O E A)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api
      (TransferIndexInspectionFacts01.keysFromBytes project prefixBytes ordinalBytes) codec index
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct available extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item))
      registryMatches exclusive .perTransaction action parent queued = some committed) :
    let keys := TransferIndexInspectionFacts01.keysFromBytes project prefixBytes ordinalBytes
    ∃ (height : Nat) (witness : TransferIndexWriterModel01.Witness),
      ∀ other, other ≠ keys.entry height witness.ordinal.val →
        other ≠ keys.identifier height witness.encoded.identifier → other ≠ keys.count height →
        committed.parent.nonverifiable other = parent.nonverifiable other := by
  obtain ⟨_, _, height, witness, _, _, _, applied, _, _⟩ :=
    TransferOrdinaryIndexDelivery01.per_transaction_success_recovers_body_height_and_index api
      (TransferIndexInspectionFacts01.keysFromBytes project prefixBytes ordinalBytes) codec index
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct available extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item)
      registryMatches exclusive action parent queued committed success
  have nv := TransferBoundOrdinarySource01.any_return_preserves_input_nonverifiable_writes raw notes volume sct available
    extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item ⟨parent, empty⟩
  refine ⟨height, witness, ?_⟩
  intro other notEntry notIdentifier notCount
  rw [applied, TransferIndexWriterModel01.apply_index_unrelated _ codec height witness parent _ other notEntry notIdentifier notCount]
  change overlay parent.nonverifiable _ other = parent.nonverifiable other
  rw [nv]
  rfl

set_option pp.all true in
#check @same_action_success_derives_visible_index_and_volume_values
#print axioms same_action_success_derives_visible_index_and_volume_values
set_option pp.all true in
#check @same_action_success_preserves_every_other_nonverifiable_key
#print axioms same_action_success_preserves_every_other_nonverifiable_key

end ShielddSecurity.TransferOrdinaryIndexedValues01
