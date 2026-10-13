import ShielddSecurity.TransferOrdinaryIndexReadSource01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferOrdinaryIndexCountSource01

open TransferStateDelta TransferRawStateProgram01
open TransferIndexWriterModel01
open TransferOrdinaryIndexReadSource01
open TransferVerificationEqualitySource01 (Item)

/-! Current-overlay count reads and enclosing Ordinary refusal. Semantic count
decode/overflow errors are derived only with successful preceding observations.
Unavailable reads merely exclude success. Codecs, byte keys, Rust storage and
native/durable correspondence remain explicit interfaces. -/

theorem successful_inspection_derives_current_count {O E A : Type}
    (keys : Keys) (codec : Codec) (convert : A → Option Encoded)
    (available : Delta O E → Nat → Bool) (height : Nat) (action : A)
    (child : Delta O E) (witness : Witness)
    (success : inspect keys codec (installReads convert available) height action child = .ok witness) :
    available child (keys.count height) = true ∧
    countObservation codec ((applyCache child.parent child.cache).nonverifiable (keys.count height)) = some witness.ordinal ∧
    witness.ordinal.val + 1 < 2 ^ 64 := by
  obtain ⟨value, _, _, read, decoded, _⟩ := TransferIndexInspectionFacts01.inspect_success_order
    keys codec (installReads convert available) height action child witness success
  have observed := successful_nv_read_derives_available_current_value available child (keys.count height) value read
  have bound := TransferIndexInspectionFacts01.inspect_success_checked_increment
    keys codec (installReads convert available) height action child witness success
  exact ⟨observed.1, observed.2 ▸ decoded, bound.2⟩

theorem available_malformed_count_derives_semantic_decode_error {O E A : Type}
    (keys : Keys) (codec : Codec) (convert : A → Option Encoded)
    (available : Delta O E → Nat → Bool) (height : Nat) (action : A)
    (child : Delta O E) (encoded : Encoded) (bytes : Bytes)
    (converted : convert action = some encoded)
    (idReadable : available child (keys.identifier height encoded.identifier) = true)
    (idAbsent : (applyCache child.parent child.cache).nonverifiable (keys.identifier height encoded.identifier) = none)
    (countReadable : available child (keys.count height) = true)
    (countPresent : (applyCache child.parent child.cache).nonverifiable (keys.count height) = some bytes)
    (malformed : codec.decodeCount bytes = none) :
    inspect keys codec (installReads convert available) height action child = .error .countDecode := by
  simp only [inspect, installReads, converted, readNV, idReadable, countReadable, ↓reduceIte,
    idAbsent, countPresent, countObservation, malformed]

theorem available_full_count_derives_semantic_overflow {O E A : Type}
    (keys : Keys) (codec : Codec) (convert : A → Option Encoded)
    (available : Delta O E → Nat → Bool) (height : Nat) (action : A)
    (child : Delta O E) (encoded : Encoded) (bytes : Bytes) (ordinal : Ordinal)
    (converted : convert action = some encoded)
    (idReadable : available child (keys.identifier height encoded.identifier) = true)
    (idAbsent : (applyCache child.parent child.cache).nonverifiable (keys.identifier height encoded.identifier) = none)
    (countReadable : available child (keys.count height) = true)
    (countPresent : (applyCache child.parent child.cache).nonverifiable (keys.count height) = some bytes)
    (decoded : codec.decodeCount bytes = some ordinal)
    (overflow : 2 ^ 64 ≤ ordinal.val + 1) :
    inspect keys codec (installReads convert available) height action child = .error .overflow := by
  simp only [inspect, installReads, converted, readNV, idReadable, countReadable, ↓reduceIte,
    idAbsent, countPresent, countObservation, decoded, nextOrdinal_overflow ordinal overflow]

theorem invalid_current_count_excludes_inspection_success {O E A : Type}
    (keys : Keys) (codec : Codec) (convert : A → Option Encoded)
    (available : Delta O E → Nat → Bool) (height : Nat) (action : A)
    (child : Delta O E) (witness : Witness)
    (invalid : countObservation codec ((applyCache child.parent child.cache).nonverifiable (keys.count height)) = none ∨
      ∃ ordinal, countObservation codec ((applyCache child.parent child.cache).nonverifiable (keys.count height)) = some ordinal ∧
        2 ^ 64 ≤ ordinal.val + 1) :
    inspect keys codec (installReads convert available) height action child ≠ .ok witness := by
  intro success
  obtain ⟨_, decoded, bound⟩ := successful_inspection_derives_current_count keys codec convert available height action child witness success
  rcases invalid with malformed | ⟨ordinal, same, overflow⟩
  · rw [malformed] at decoded
    contradiction
  · have equal : witness.ordinal = ordinal := Option.some.inj (decoded.symm.trans same)
    rw [equal] at bound
    exact (Nat.not_lt.mpr overflow) bound

theorem invalid_parent_count_rejects_whole_ordinary_delivery {O E K X Tree A : Type}
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
    (encodedHeight : Bytes)
    (storedHeight : parent.verifiable (project TransferVolumeHeightKeys01.heightBytes) = some encodedHeight)
    (decodedHeight : decode encodedHeight = some height)
    (invalid : countObservation codec (parent.nonverifiable (keys.count height)) = none ∨
      ∃ ordinal, countObservation codec (parent.nonverifiable (keys.count height)) = some ordinal ∧ 2 ^ 64 ≤ ordinal.val + 1) :
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
    have currentCount : (applyCache parent
        (TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
          treeKey notesKey volumeKey payload nullifierKey (project (TransferVolumeHeightKeys01.entryBytes entrySuffix))
          (project (TransferVolumeHeightKeys01.dayBytes daySuffix)) action item ⟨parent, empty⟩).cache).nonverifiable
        (keys.count height) = parent.nonverifiable (keys.count height) := by
      change overlay parent.nonverifiable _ (keys.count height) = parent.nonverifiable (keys.count height)
      rw [nv]
      rfl
    exact False.elim ((invalid_current_count_excludes_inspection_success keys codec convert indexAvailable height action _ witness
      (currentCount.symm ▸ invalid)) inspected)

theorem invalid_parent_count_preserves_parent_and_queue {O E K X Tree A : Type}
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
    (encodedHeight : Bytes)
    (storedHeight : parent.verifiable (project TransferVolumeHeightKeys01.heightBytes) = some encodedHeight)
    (decodedHeight : decode encodedHeight = some height)
    (invalid : countObservation codec (parent.nonverifiable (keys.count height)) = none ∨
      ∃ ordinal, countObservation codec (parent.nonverifiable (keys.count height)) = some ordinal ∧ 2 ^ 64 ≤ ordinal.val + 1) :
    finish parent queued (run (TransferOrdinaryIndexDelivery01.combinedApi
      (TransferOrdinaryHeightSource01.withHeight api heightAvailable decode (project TransferVolumeHeightKeys01.heightBytes))
      keys codec (installReads convert indexAvailable)
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey (project (TransferVolumeHeightKeys01.entryBytes entrySuffix))
        (project (TransferVolumeHeightKeys01.dayBytes daySuffix)) action item))
      registryMatches exclusive .perTransaction action parent queued) = (parent, queued) := by
  exact delivery_failure_preserves_parent_and_queue _ _ _ _ _ _ _
    (invalid_parent_count_rejects_whole_ordinary_delivery api keys codec convert indexAvailable heightAvailable volumeAvailable
      decode project injection entrySuffix daySuffix raw notes volume sct extract inputs outputs wordMax capacity treeKey notesKey
      volumeKey payload nullifierKey height action item registryMatches exclusive parent queued encodedHeight
      storedHeight decodedHeight invalid)

set_option pp.all true in
#check @successful_inspection_derives_current_count
#print axioms successful_inspection_derives_current_count
set_option pp.all true in
#check @available_malformed_count_derives_semantic_decode_error
#print axioms available_malformed_count_derives_semantic_decode_error
set_option pp.all true in
#check @available_full_count_derives_semantic_overflow
#print axioms available_full_count_derives_semantic_overflow
set_option pp.all true in
#check @invalid_current_count_excludes_inspection_success
#print axioms invalid_current_count_excludes_inspection_success
set_option pp.all true in
#check @invalid_parent_count_rejects_whole_ordinary_delivery
#print axioms invalid_parent_count_rejects_whole_ordinary_delivery
set_option pp.all true in
#check @invalid_parent_count_preserves_parent_and_queue
#print axioms invalid_parent_count_preserves_parent_and_queue

end ShielddSecurity.TransferOrdinaryIndexCountSource01
