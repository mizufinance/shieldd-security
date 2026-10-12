import ShielddSecurity.TransferOrdinaryMaxCount01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferOrdinaryDecodableIndex01
open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01
open TransferOrdinaryIndexReadSource01
open TransferVerificationEqualitySource01 (Item)

/-! Concrete ordinal key/value encoding and current NV reads are installed in
same-action Ordinary delivery. Success derives readable mathematical u64 index
values, rather than assuming codec or desired stored-value postconditions.
Rust byte/key/store/ownership/proof/crypto/native/durability remain interfaces. -/

theorem whole_success_derives_decodable_u64_index_values {O E K X Tree A : Type}
    (api : Api O E A) (project : Bytes → Nat) (injection : Function.Injective project)
    (prefixBytes : Nat → Bytes) (entrySuffix daySuffix : Bytes)
    (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey : Nat)
    (action : A) (item : Item) (registryMatches exclusive : Bool) (parent : State O)
    (queued : List A) (committed : Commit O E A)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api
      (TransferIndexInspectionFacts01.keysFromBytes project prefixBytes (TransferIndexCountCodec01.encodeBE 8))
      TransferIndexCountCodec01.codec (installReads convert indexAvailable)
      (TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
        treeKey notesKey volumeKey payload nullifierKey (project (TransferVolumeHeightKeys01.entryBytes entrySuffix))
        (project (TransferVolumeHeightKeys01.dayBytes daySuffix)) action item))
      registryMatches exclusive .perTransaction action parent queued = some committed) :
    let keys := TransferIndexInspectionFacts01.keysFromBytes project prefixBytes (TransferIndexCountCodec01.encodeBE 8)
    ∃ (height : Nat) (witness : Witness) (idBytes countBytes : Bytes),
      extract action .ordinary = .ok item ∧ convert action = some witness.encoded ∧
      witness.next.val = witness.ordinal.val + 1 ∧ witness.ordinal.val + 1 < 2 ^ 64 ∧
      parent.verifiable (project (TransferVolumeHeightKeys01.entryBytes entrySuffix)) = none ∧
      committed.parent.verifiable (project (TransferVolumeHeightKeys01.entryBytes entrySuffix)) = some [1] ∧
      committed.parent.verifiable (project (TransferVolumeHeightKeys01.dayBytes daySuffix)) = some [1] ∧
      committed.parent.nonverifiable (keys.entry height witness.ordinal.val) = some witness.encoded.payload ∧
      committed.parent.nonverifiable (keys.identifier height witness.encoded.identifier) = some idBytes ∧
      committed.parent.nonverifiable (keys.count height) = some countBytes ∧
      idBytes.length = 8 ∧ countBytes.length = 8 ∧
      TransferIndexCountCodec01.validBytes idBytes = true ∧ TransferIndexCountCodec01.validBytes countBytes = true ∧
      TransferIndexCountCodec01.codec.decodeCount idBytes = some witness.ordinal ∧
      TransferIndexCountCodec01.codec.decodeCount countBytes = some witness.next ∧ committed.deferred = queued := by
  have separate := TransferVolumeHeightKeys01.projected_source_keys_separate project injection entrySuffix daySuffix
  obtain ⟨height, witness, extracted, converted, increment, bound, fresh, entry, day, payloadValue, identifierValue, countValue, queue⟩ :=
    TransferOrdinaryIndexedValues01.same_action_success_derives_visible_index_and_volume_values api project injection prefixBytes
      (TransferIndexCountCodec01.encodeBE 8) TransferIndexCountCodec01.codec (installReads convert indexAvailable)
      raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload nullifierKey
      (project (TransferVolumeHeightKeys01.entryBytes entrySuffix)) (project (TransferVolumeHeightKeys01.dayBytes daySuffix))
      action item registryMatches exclusive parent queued committed separate.2.2 success
  refine ⟨height, witness, TransferIndexCountCodec01.codec.encodeCount witness.ordinal,
    TransferIndexCountCodec01.codec.encodeCount witness.next, extracted, converted, increment, bound,
    fresh, entry, day, payloadValue, identifierValue, countValue, ?_, ?_, ?_, ?_,
    TransferIndexCountCodec01.codec_roundtrip witness.ordinal, TransferIndexCountCodec01.codec_roundtrip witness.next, queue⟩
  · exact TransferIndexCountCodec01.encode_length 8 witness.ordinal.val
  · exact TransferIndexCountCodec01.encode_length 8 witness.next.val
  · exact TransferIndexCountCodec01.encode_valid 8 witness.ordinal.val witness.ordinal.isLt
  · exact TransferIndexCountCodec01.encode_valid 8 witness.next.val witness.next.isLt

set_option pp.all true in
#check @whole_success_derives_decodable_u64_index_values
#print axioms whole_success_derives_decodable_u64_index_values
end ShielddSecurity.TransferOrdinaryDecodableIndex01
