import ShielddSecurity.TransferVolumeHeightKeys01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferOrdinaryIndexReadSource01

open TransferStateDelta TransferRawStateProgram01
open TransferIndexWriterModel01 (Keys Codec Backend Encoded Witness)
open TransferVerificationEqualitySource01 (Item)

/-! Install actual modeled current-overlay NV reads in the index program.
Read failure differs from absence; every present value is an existing ID.
Ordinary body NV framing and source height/key framing derive whole delivery
refusal from an original parent ID entry without assuming successful body,
desired index error, stable height callback or rollback poststate. Real Rust
nonverifiable_get_raw/get_proto/codec/key/ownership/proof/durability remain
interfaces. Native semantic controls remain separate and unexecuted. -/

def readNV {O E : Type} (available : Delta O E → Nat → Bool)
    (child : Delta O E) (key : Nat) : Option (Option Bytes) :=
  if available child key then some ((applyCache child.parent child.cache).nonverifiable key) else none

def installReads {O E A : Type} (convert : A → Option Encoded)
    (available : Delta O E → Nat → Bool) : Backend O E A :=
  ⟨convert, readNV available⟩

theorem successful_nv_read_derives_available_current_value {O E : Type}
    (available : Delta O E → Nat → Bool) (child : Delta O E) (key : Nat) (value : Option Bytes)
    (success : readNV available child key = some value) :
    available child key = true ∧ (applyCache child.parent child.cache).nonverifiable key = value := by
  cases readable : available child key with
  | false => simp [readNV, readable] at success
  | true =>
    have same : some ((applyCache child.parent child.cache).nonverifiable key) = some value := by
      simpa only [readNV, readable, ↓reduceIte] using success
    exact ⟨rfl, Option.some.inj same⟩

theorem available_existing_id_derives_semantic_duplicate {O E A : Type}
    (keys : Keys) (codec : Codec) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (action : A) (child : Delta O E) (encoded : Encoded) (previous : Bytes)
    (converted : convert action = some encoded)
    (readable : available child (keys.identifier height encoded.identifier) = true)
    (present : (applyCache child.parent child.cache).nonverifiable (keys.identifier height encoded.identifier) = some previous) :
    TransferIndexWriterModel01.inspect keys codec (installReads convert available) height action child = .error .duplicate := by
  simp only [TransferIndexWriterModel01.inspect, installReads, converted, readNV, readable, ↓reduceIte, present]

theorem existing_id_excludes_index_success {O E A : Type}
    (keys : Keys) (codec : Codec) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (action : A) (child : Delta O E) (encoded : Encoded) (previous : Bytes)
    (converted : convert action = some encoded)
    (present : (applyCache child.parent child.cache).nonverifiable (keys.identifier height encoded.identifier) = some previous)
    (witness : Witness) :
    TransferIndexWriterModel01.inspect keys codec (installReads convert available) height action child ≠ .ok witness := by
  cases readable : available child (keys.identifier height encoded.identifier) with
  | false => simp [TransferIndexWriterModel01.inspect, installReads, converted, readNV, readable]
  | true =>
    rw [available_existing_id_derives_semantic_duplicate keys codec convert available height action child encoded previous converted readable present]
    intro impossible
    contradiction

theorem existing_parent_id_rejects_whole_ordinary_delivery {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (codec : Codec) (convert : A → Option Encoded)
    (indexAvailable : Delta O E → Nat → Bool) (heightAvailable volumeAvailable : Delta O E → Bool)
    (decode : Bytes → Option Nat) (project : Bytes → Nat) (injection : Function.Injective project)
    (entrySuffix daySuffix : Bytes)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey height : Nat)
    (action : A) (item : Item) (registryMatches exclusive : Bool) (parent : State O) (queued : List A)
    (encoded : Encoded) (previous encodedHeight : Bytes)
    (converted : convert action = some encoded)
    (storedHeight : parent.verifiable (project TransferVolumeHeightKeys01.heightBytes) = some encodedHeight)
    (decodedHeight : decode encodedHeight = some height)
    (duplicate : parent.nonverifiable (keys.identifier height encoded.identifier) = some previous) :
    run (TransferOrdinaryIndexDelivery01.combinedApi
      (TransferOrdinaryHeightSource01.withHeight api heightAvailable decode (project TransferVolumeHeightKeys01.heightBytes))
      keys codec (installReads convert indexAvailable)
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey (project (TransferVolumeHeightKeys01.entryBytes entrySuffix))
        (project (TransferVolumeHeightKeys01.dayBytes daySuffix)) action item))
      registryMatches exclusive .perTransaction action parent queued = none := by
  cases result : run (TransferOrdinaryIndexDelivery01.combinedApi
      (TransferOrdinaryHeightSource01.withHeight api heightAvailable decode (project TransferVolumeHeightKeys01.heightBytes))
      keys codec (installReads convert indexAvailable)
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey (project (TransferVolumeHeightKeys01.entryBytes entrySuffix))
        (project (TransferVolumeHeightKeys01.dayBytes daySuffix)) action item))
      registryMatches exclusive .perTransaction action parent queued with
  | none => rfl
  | some committed =>
    have separate := TransferVolumeHeightKeys01.projected_source_keys_separate project injection entrySuffix daySuffix
    obtain ⟨actualHeight, actualBytes, witness, original, decoded, _, inspected, _⟩ :=
      TransferOrdinaryHeightSource01.whole_indexed_success_derives_original_parent_height api keys codec
        (installReads convert indexAvailable) heightAvailable volumeAvailable decode raw notes volume sct extract inputs outputs
        wordMax capacity treeKey notesKey volumeKey payload nullifierKey
        (project (TransferVolumeHeightKeys01.entryBytes entrySuffix)) (project (TransferVolumeHeightKeys01.dayBytes daySuffix))
        (project TransferVolumeHeightKeys01.heightBytes) action item registryMatches exclusive parent queued committed separate.1 separate.2.1 result
    have sameBytes : actualBytes = encodedHeight := Option.some.inj (original.symm.trans storedHeight)
    subst actualBytes
    have sameHeight : actualHeight = height := Option.some.inj (decoded.symm.trans decodedHeight)
    subst actualHeight
    have nv := TransferBoundOrdinarySource01.any_return_preserves_input_nonverifiable_writes raw notes volume sct volumeAvailable
      extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload nullifierKey
      (project (TransferVolumeHeightKeys01.entryBytes entrySuffix)) (project (TransferVolumeHeightKeys01.dayBytes daySuffix))
      action item ⟨parent, empty⟩
    have currentDuplicate : (applyCache parent
        (TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
          treeKey notesKey volumeKey payload nullifierKey (project (TransferVolumeHeightKeys01.entryBytes entrySuffix))
          (project (TransferVolumeHeightKeys01.dayBytes daySuffix)) action item ⟨parent, empty⟩).cache).nonverifiable
        (keys.identifier height encoded.identifier) = some previous := by
      change overlay parent.nonverifiable _ (keys.identifier height encoded.identifier) = some previous
      rw [nv]
      exact duplicate
    exact False.elim ((existing_id_excludes_index_success keys codec convert indexAvailable height action _ encoded previous
      converted currentDuplicate witness) inspected)

theorem existing_parent_id_preserves_parent_and_queue {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (codec : Codec) (convert : A → Option Encoded)
    (indexAvailable : Delta O E → Nat → Bool) (heightAvailable volumeAvailable : Delta O E → Bool)
    (decode : Bytes → Option Nat) (project : Bytes → Nat) (injection : Function.Injective project)
    (entrySuffix daySuffix : Bytes)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey height : Nat)
    (action : A) (item : Item) (registryMatches exclusive : Bool) (parent : State O) (queued : List A)
    (encoded : Encoded) (previous encodedHeight : Bytes)
    (converted : convert action = some encoded)
    (storedHeight : parent.verifiable (project TransferVolumeHeightKeys01.heightBytes) = some encodedHeight)
    (decodedHeight : decode encodedHeight = some height)
    (duplicate : parent.nonverifiable (keys.identifier height encoded.identifier) = some previous) :
    finish parent queued (run (TransferOrdinaryIndexDelivery01.combinedApi
      (TransferOrdinaryHeightSource01.withHeight api heightAvailable decode (project TransferVolumeHeightKeys01.heightBytes))
      keys codec (installReads convert indexAvailable)
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey (project (TransferVolumeHeightKeys01.entryBytes entrySuffix))
        (project (TransferVolumeHeightKeys01.dayBytes daySuffix)) action item))
      registryMatches exclusive .perTransaction action parent queued) = (parent, queued) := by
  exact delivery_failure_preserves_parent_and_queue _ _ _ _ _ _ _
    (existing_parent_id_rejects_whole_ordinary_delivery api keys codec convert indexAvailable heightAvailable volumeAvailable
      decode project injection entrySuffix daySuffix raw notes volume sct extract inputs outputs wordMax capacity treeKey notesKey
      volumeKey payload nullifierKey height action item registryMatches exclusive parent queued encoded previous encodedHeight
      converted storedHeight decodedHeight duplicate)

set_option pp.all true in
#check @readNV
#print axioms readNV
set_option pp.all true in
#check @installReads
#print axioms installReads
set_option pp.all true in
#check @successful_nv_read_derives_available_current_value
#print axioms successful_nv_read_derives_available_current_value
set_option pp.all true in
#check @available_existing_id_derives_semantic_duplicate
#print axioms available_existing_id_derives_semantic_duplicate
set_option pp.all true in
#check @existing_id_excludes_index_success
#print axioms existing_id_excludes_index_success
set_option pp.all true in
#check @existing_parent_id_rejects_whole_ordinary_delivery
#print axioms existing_parent_id_rejects_whole_ordinary_delivery
set_option pp.all true in
#check @existing_parent_id_preserves_parent_and_queue
#print axioms existing_parent_id_preserves_parent_and_queue

end ShielddSecurity.TransferOrdinaryIndexReadSource01
