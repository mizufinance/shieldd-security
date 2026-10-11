import ShielddSecurity.TransferNativePendingWrite01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferNativeRawPending01
open TransferStateDelta TransferNullifierBatchSource01
open TransferPendingFiniteCodec01 (NativePending erase)
open TransferPendingSetInvariant01 (Invariant)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject BoundedPending nativeSupported nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)

/-! Bind the accepted fixed finite codec to the primitive and actual modeled
raw reshape. Supported writes follow from the codec definition, without an
extra encoder equality hypothesis. Later note/SCT results frame the pending
object on every returned outcome, including errors. No whole raw/commit
success is needed, and the failed child is not asserted published. Native
typed codec/getter/Clone/finite library, input projection and actual trace,
key identity, ownership/reader/crypto/OS remain separate interfaces. -/

def nativeRaw {O E X : Type} (encodeNative : NativePending → O)
    (raw : TransferRawEffectsSource01.Backend (ExtendedObject O) E X) :
    TransferRawEffectsSource01.Backend (ExtendedObject O) E X :=
  {raw with nullifiers := {raw.nullifiers with encode := TransferPendingFiniteCodec01.encode (encodeObject encodeNative)}}

theorem fixed_codec_successful_primitive_derives_native_write_without_encoder_premise {O E X : Type}
    (encodeNative : NativePending → O) (raw : TransferRawEffectsSource01.Backend (ExtendedObject O) E X)
    (wordMax objectKey : Nat) (sourceHasId : Bool) (child : Delta (ExtendedObject O) E)
    (keys : List Nat) (cache : Cache (ExtendedObject O) E)
    (initial : Invariant blockCapacity (raw.nullifiers.pending child))
    (bounded : BoundedPending (raw.nullifiers.pending child))
    (inputs : ∀ key ∈ keys, key < nullifierModulus) (belowWord : blockCapacity < wordMax)
    (nonempty : keys.isEmpty = false)
    (passed : executeNullify (nativeRaw encodeNative raw).nullifiers wordMax blockCapacity objectKey sourceHasId child keys = ⟨cache, .ok ()⟩) :
    sourceHasId = true ∧ ∃ (next : Pending),
      inspect raw.nullifiers wordMax blockCapacity child keys = .ok next ∧
      Invariant blockCapacity next ∧ BoundedPending next ∧ nativeSupported (erase next) = true ∧
      cache = (putObject child objectKey (some (.inl (encodeNative (erase next))))).cache ∧
      (applyCache child.parent cache).objects objectKey = some (.inl (encodeNative (erase next))) := by
  exact TransferNativePendingWrite01.successful_nonempty_primitive_writes_actual_supported_native_object
    (fun native => .inl (encodeNative native)) (nativeRaw encodeNative raw).nullifiers
    (fun pending _ lengthBound valueBound =>
      TransferBoundedNativeCodec01.supported_pending_encoding_is_actual_native_branch encodeNative pending lengthBound valueBound)
    wordMax objectKey sourceHasId child keys cache initial bounded inputs belowWord nonempty passed

theorem any_returned_raw_reshape_retains_supported_native_pending_after_primitive_success {O E X Tree : Type}
    (encodeNative : NativePending → O)
    (raw : TransferRawEffectsSource01.Backend (ExtendedObject O) E (TransferSctInsertionSource01.Error X))
    (notes : TransferNoteManagerSource01.Backend (ExtendedObject O) E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend (ExtendedObject O) E X Tree)
    (wordMax treeKey notesKey pendingKey : Nat) (sourceHasId : Bool) (child : Delta (ExtendedObject O) E)
    (inputs outputs : List Nat) (cache : Cache (ExtendedObject O) E)
    (initial : Invariant blockCapacity (raw.nullifiers.pending child))
    (bounded : BoundedPending (raw.nullifiers.pending child))
    (nativeInputs : ∀ key ∈ inputs, key < nullifierModulus) (belowWord : blockCapacity < wordMax)
    (nonempty : inputs.isEmpty = false) (notTree : pendingKey ≠ treeKey) (notNotes : pendingKey ≠ notesKey)
    (source : raw.currentSource child = some sourceHasId)
    (passed : executeNullify (nativeRaw encodeNative raw).nullifiers wordMax blockCapacity pendingKey sourceHasId child inputs = ⟨cache, .ok ()⟩) :
    ∃ (next : Pending), inspect raw.nullifiers wordMax blockCapacity child inputs = .ok next ∧
      Invariant blockCapacity next ∧ BoundedPending next ∧ nativeSupported (erase next) = true ∧
      (TransferRawEffectsSource01.reshape (TransferRawSourceFrames01.installNotes (nativeRaw encodeNative raw) notes sct treeKey notesKey)
        wordMax blockCapacity pendingKey child inputs outputs).cache.objects pendingKey =
        some (some (.inl (encodeNative (erase next)))) := by
  obtain ⟨_, next, inspected, nextInvariant, nextBounded, supported, written, _⟩ :=
    fixed_codec_successful_primitive_derives_native_write_without_encoder_premise
      encodeNative raw wordMax pendingKey sourceHasId child inputs cache initial bounded nativeInputs belowWord nonempty passed
  have framed := TransferPendingNullifierRetention01.all_notes_any_return_frames_other_object
    (nativeRaw encodeNative raw) notes sct treeKey notesKey pendingKey sourceHasId
    {child with cache := TransferRawEffectsSource01.emitSpends raw.spentEvent cache inputs} outputs notTree notNotes
  have staged : (TransferRawEffectsSource01.emitSpends raw.spentEvent cache inputs).objects pendingKey =
      some (some (.inl (encodeNative (erase next)))) := by
    rw [TransferRawEffectsSource01.emitSpends_exact, written]
    simp only [putObject, ite_true]
  refine ⟨next, inspected, nextInvariant, nextBounded, supported, ?_⟩
  simpa only [TransferRawEffectsSource01.reshape, TransferRawSourceFrames01.installNotes,
    TransferNoteManagerSource01.installNotes, nativeRaw, source, passed] using framed.trans staged

set_option pp.all true in
#check @nativeRaw
#print axioms nativeRaw
set_option pp.all true in
#check @fixed_codec_successful_primitive_derives_native_write_without_encoder_premise
#print axioms fixed_codec_successful_primitive_derives_native_write_without_encoder_premise
set_option pp.all true in
#check @any_returned_raw_reshape_retains_supported_native_pending_after_primitive_success
#print axioms any_returned_raw_reshape_retains_supported_native_pending_after_primitive_success
end ShielddSecurity.TransferNativeRawPending01
