import ShielddSecurity.TransferNativeRawPending01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferNativeGhostErasure01
open TransferStateDelta TransferRawStateProgram01 TransferNullifierBatchSource01
open TransferPendingFiniteCodec01 (NativePending erase)
open TransferPendingSetInvariant01 (Invariant)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject BoundedPending nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferNativeRawPending01 (nativeRaw)

/-! Exact source-model erasure of unsupported ghost pending encodings on
bounded canonical primitive/raw paths, including all returned error outcomes.
The native-only comparison encoder always selects the native sum branch;
unsupported arguments are never used by an actual successful inspection.
Both versions reuse identical actual note/volume callbacks and observations.
This is symbolic model equality, not a Rust execution trace or proof of native
codec/getter/finite library/input/callback/ownership/OS correspondence. -/

def nativeOnlyRaw {O E X : Type} (encodeNative : NativePending → O)
    (raw : TransferRawEffectsSource01.Backend (ExtendedObject O) E X) :
    TransferRawEffectsSource01.Backend (ExtendedObject O) E X :=
  {raw with nullifiers := {raw.nullifiers with encode := fun pending => .inl (encodeNative (erase pending))}}

theorem bounded_primitive_ghost_erasure_preserves_every_returned_outcome {O E X : Type}
    (encodeNative : NativePending → O) (raw : TransferRawEffectsSource01.Backend (ExtendedObject O) E X)
    (wordMax objectKey : Nat) (sourceHasId : Bool) (child : Delta (ExtendedObject O) E) (keys : List Nat)
    (initial : Invariant blockCapacity (raw.nullifiers.pending child))
    (bounded : BoundedPending (raw.nullifiers.pending child))
    (inputs : ∀ key ∈ keys, key < nullifierModulus) (belowWord : blockCapacity < wordMax) :
    executeNullify (nativeRaw encodeNative raw).nullifiers wordMax blockCapacity objectKey sourceHasId child keys =
      executeNullify (nativeOnlyRaw encodeNative raw).nullifiers wordMax blockCapacity objectKey sourceHasId child keys := by
  have inspection : inspect (nativeRaw encodeNative raw).nullifiers wordMax blockCapacity child keys =
      inspect raw.nullifiers wordMax blockCapacity child keys := rfl
  have inspectionOnly : inspect (nativeOnlyRaw encodeNative raw).nullifiers wordMax blockCapacity child keys =
      inspect raw.nullifiers wordMax blockCapacity child keys := rfl
  cases empty : keys.isEmpty with
  | true => simp only [executeNullify, empty, if_true]
  | false =>
    cases sourceHasId with
    | false => simp only [executeNullify, empty, Bool.false_eq_true, if_false]
    | true =>
      cases checked : inspect raw.nullifiers wordMax blockCapacity child keys with
      | error error => simp only [executeNullify, empty, Bool.false_eq_true, if_false, if_true, inspection, inspectionOnly, checked]
      | ok next =>
        have derived := TransferNativePendingWrite01.successful_primitive_inspection_derives_supported_native_next
          raw.nullifiers wordMax child keys next initial bounded inputs belowWord checked
        have encoded := TransferBoundedNativeCodec01.supported_pending_encoding_is_actual_native_branch
          encodeNative next derived.1.2.2.1 derived.2.1
        simp only [executeNullify, empty, Bool.false_eq_true, if_false, if_true, inspection, inspectionOnly, checked]
        change (⟨(putObject child objectKey (some (TransferPendingFiniteCodec01.encode (encodeObject encodeNative) next))).cache,
          .ok ()⟩ : Outcome (ExtendedObject O) E BatchError) = ⟨(putObject child objectKey (some (.inl (encodeNative (erase next))))).cache, .ok ()⟩
        rw [encoded]

theorem notes_ignore_the_erased_nullifier_encoder {O E X : Type}
    (encodeNative : NativePending → O) (raw : TransferRawEffectsSource01.Backend (ExtendedObject O) E X)
    (source : Bool) (child : Delta (ExtendedObject O) E) (outputs : List Nat) :
    TransferRawEffectsSource01.notes (nativeRaw encodeNative raw) source child outputs =
      TransferRawEffectsSource01.notes (nativeOnlyRaw encodeNative raw) source child outputs := by
  induction outputs generalizing child with
  | nil => rfl
  | cons output rest ih =>
    change next (TransferRawEffectsSource01.liftCallback (raw.noteInsert child source output))
      (fun updated => TransferRawEffectsSource01.notes (nativeRaw encodeNative raw) source
        {child with cache := TransferRawEffectsSource01.emit updated (raw.noteEvent output)} rest) =
      next (TransferRawEffectsSource01.liftCallback (raw.noteInsert child source output))
        (fun updated => TransferRawEffectsSource01.notes (nativeOnlyRaw encodeNative raw) source
          {child with cache := TransferRawEffectsSource01.emit updated (raw.noteEvent output)} rest)
    cases result : (raw.noteInsert child source output).result with
    | error error => simp only [next, TransferRawEffectsSource01.liftCallback, result]
    | ok returnedUnit =>
      cases returnedUnit
      simpa only [next, TransferRawEffectsSource01.liftCallback, result] using
        ih {child with cache := TransferRawEffectsSource01.emit (raw.noteInsert child source output).cache (raw.noteEvent output)}

theorem bounded_raw_reshape_ghost_erasure_preserves_every_returned_outcome {O E X : Type}
    (encodeNative : NativePending → O) (raw : TransferRawEffectsSource01.Backend (ExtendedObject O) E X)
    (wordMax objectKey : Nat) (child : Delta (ExtendedObject O) E) (inputs outputs : List Nat)
    (initial : Invariant blockCapacity (raw.nullifiers.pending child))
    (bounded : BoundedPending (raw.nullifiers.pending child))
    (nativeInputs : ∀ key ∈ inputs, key < nullifierModulus) (belowWord : blockCapacity < wordMax) :
    TransferRawEffectsSource01.reshape (nativeRaw encodeNative raw) wordMax blockCapacity objectKey child inputs outputs =
      TransferRawEffectsSource01.reshape (nativeOnlyRaw encodeNative raw) wordMax blockCapacity objectKey child inputs outputs := by
  cases source : raw.currentSource child with
  | none => simp only [TransferRawEffectsSource01.reshape, nativeRaw, nativeOnlyRaw, source]
  | some sourceHasId =>
    have primitive := bounded_primitive_ghost_erasure_preserves_every_returned_outcome
      encodeNative raw wordMax objectKey sourceHasId child inputs initial bounded nativeInputs belowWord
    have extendedSource : (nativeRaw encodeNative raw).currentSource child = some sourceHasId := source
    have onlySource : (nativeOnlyRaw encodeNative raw).currentSource child = some sourceHasId := source
    simp only [TransferRawEffectsSource01.reshape, extendedSource, onlySource]
    rw [primitive]
    cases observed : executeNullify (nativeOnlyRaw encodeNative raw).nullifiers wordMax blockCapacity objectKey sourceHasId child inputs with
    | mk cache result =>
      cases result with
      | error error => rfl
      | ok returnedUnit =>
        cases returnedUnit
        exact notes_ignore_the_erased_nullifier_encoder encodeNative raw sourceHasId
          {child with cache := TransferRawEffectsSource01.emitSpends raw.spentEvent cache inputs} outputs


theorem bounded_raw_transfer_ghost_erasure_preserves_every_returned_outcome {O E X : Type}
    (encodeNative : NativePending → O) (raw : TransferRawEffectsSource01.Backend (ExtendedObject O) E X)
    (wordMax objectKey entryKey dayKey : Nat) (exactMatched ordinary : Bool)
    (child : Delta (ExtendedObject O) E) (inputs outputs : List Nat)
    (initial : Invariant blockCapacity (raw.nullifiers.pending child))
    (bounded : BoundedPending (raw.nullifiers.pending child))
    (nativeInputs : ∀ key ∈ inputs, key < nullifierModulus) (belowWord : blockCapacity < wordMax) :
    TransferRawEffectsSource01.executeTransfer (nativeRaw encodeNative raw) wordMax blockCapacity objectKey entryKey dayKey exactMatched ordinary child inputs outputs =
      TransferRawEffectsSource01.executeTransfer (nativeOnlyRaw encodeNative raw) wordMax blockCapacity objectKey entryKey dayKey exactMatched ordinary child inputs outputs := by
  have reshaped := bounded_raw_reshape_ghost_erasure_preserves_every_returned_outcome
    encodeNative raw wordMax objectKey child inputs outputs initial bounded nativeInputs belowWord
  have tail : ∀ current, TransferRawEffectsSource01.volumeTail (nativeRaw encodeNative raw) entryKey dayKey ordinary current =
      TransferRawEffectsSource01.volumeTail (nativeOnlyRaw encodeNative raw) entryKey dayKey ordinary current := fun _ => rfl
  simp only [TransferRawEffectsSource01.executeTransfer, reshaped, tail]

set_option pp.all true in
#check @nativeOnlyRaw
#print axioms nativeOnlyRaw
set_option pp.all true in
#check @bounded_primitive_ghost_erasure_preserves_every_returned_outcome
#print axioms bounded_primitive_ghost_erasure_preserves_every_returned_outcome
set_option pp.all true in
#check @notes_ignore_the_erased_nullifier_encoder
#print axioms notes_ignore_the_erased_nullifier_encoder
set_option pp.all true in
#check @bounded_raw_reshape_ghost_erasure_preserves_every_returned_outcome
#print axioms bounded_raw_reshape_ghost_erasure_preserves_every_returned_outcome
set_option pp.all true in
#check @bounded_raw_transfer_ghost_erasure_preserves_every_returned_outcome
#print axioms bounded_raw_transfer_ghost_erasure_preserves_every_returned_outcome
end ShielddSecurity.TransferNativeGhostErasure01
