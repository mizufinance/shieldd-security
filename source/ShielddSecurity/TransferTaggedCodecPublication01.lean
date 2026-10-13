import ShielddSecurity.TransferNativeGetterPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferTaggedCodecPublication01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending restore)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject nativeSupported nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request allInputs)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferSourceTypedInputProjection01 (typedWords installTypedInputs)
open TransferKnownFinalizerPublication01 (Effects installIo)
open TransferInstalledSourcePublication01 (SourceRequest installRequests)
open TransferInjectiveKeyPublication01 (keyCode)
open TransferFinalizationObjectFrames01 (Mutation)
open TransferFixedFinalizerPublication01 (FinalizationWrites installFixedIo)
open TransferPendingSetInvariant01 (Invariant)
open TransferBoundedNativeCodec01 (BoundedPending)
open TransferBlockPendingSequence01 (parentPending)
open TransferNativeGetterPublication01 (installGetterIo)
/-! Heterogeneous typed source-model objects distinguish native pending enum
from every other native object. Encoding injects the enum tag; decoding that
tag recovers the exact enum, and other tags restore the default empty enum.
Native cached tree uses the other-object tag. Model roundtrip is proved with
no caller codec hypothesis; native Any/downcast/Clone/finite enum/field/cache
and full trace correspondence remain explicit. Ghost-extended carrier still
exists in the old source closure; no global ghost erasure/native credit. -/

def TaggedObject (Other : Type) : Type := NativePending ⊕ Other

def encodePending {Other : Type} (native : NativePending) : TaggedObject Other := .inl native

def decodePending {Other : Type} : TaggedObject Other → NativePending
  | .inl native => native
  | .inr _ => .opened [] []

structure OtherFinalizationWrites (Other E A : Type) where
  nativeTreeObject : Other
  verifiable : Writes Bytes
  nonverifiable : Writes Bytes
  events : List E
  queued : List A

def liftWrites {Other E A : Type} (writes : OtherFinalizationWrites Other E A) : FinalizationWrites (TaggedObject Other) E A :=
  ⟨.inr writes.nativeTreeObject, writes.verifiable, writes.nonverifiable, writes.events, writes.queued⟩

def installTaggedIo {Other E A : Type}
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (TaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A) : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A :=
  installGetterIo encodePending decodePending (fun height state queued => liftWrites (writesOf height state queued)) baseIo

theorem tagged_pending_restore_roundtrip {Other : Type} (native : NativePending) :
    restore (decodePending (encodePending (Other := Other) native)) = restore native := rfl

theorem tagged_codec_source_finalization_publishes_exact_global_mathematical_input_vector {Other E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject (TaggedObject Other)) E K X Tree A I inputs))
    (parent : State (ExtendedObject (TaggedObject Other))) (queued : List A) (final : State (ExtendedObject (TaggedObject Other)) × List A)
    (storedNativeDefault : parent.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (encodePending (.opened [] []))))
    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodePending)
      (TransferPendingFiniteCodec01.decode (decodeObject decodePending)) keyCode parent queued (installRequests inputs wordOf sourceRequests) = some final)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (TaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject (TaggedObject Other)))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (success : (TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) host height final.2).root = some root) :
    allInputs (installRequests inputs wordOf sourceRequests) = (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
    ∃ state,
      (TransferHostEndBlock01.transferred (installTaggedIo writesOf baseIo).ending host height final.2).returned = some state ∧
      state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = some (.inl (encodePending (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) ∧
      (allInputs (installRequests inputs wordOf sourceRequests)).Nodup ∧ (allInputs (installRequests inputs wordOf sourceRequests)).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs (installRequests inputs wordOf sourceRequests), key < nullifierModulus) ∧
      ∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted = allInputs (installRequests inputs wordOf sourceRequests) ∧ frozen.next.applicationRoot = some root ∧
        (TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) host height final.2).host.writer = .ready frozen.next ∧
        (TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) host height final.2).host.phase = .idle ∧
        (TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
        (TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) host height final.2).host.store.boundary = some frozen.next.nullifiers := by
  exact TransferNativeGetterPublication01.native_getter_source_finalization_publishes_exact_global_mathematical_input_vector
    (encodePending (Other := Other)) (decodePending (Other := Other))
    (fun native _ => tagged_pending_restore_roundtrip native)
    inputs wordOf sourceRequests parent queued final storedNativeDefault walkedNative
    (fun height state queued => liftWrites (writesOf height state queued)) baseIo host height root currentState success
set_option pp.all true in
#check @TaggedObject
#print axioms TaggedObject
set_option pp.all true in
#check @encodePending
#print axioms encodePending
set_option pp.all true in
#check @decodePending
#print axioms decodePending
set_option pp.all true in
#check @OtherFinalizationWrites
#print axioms OtherFinalizationWrites
set_option pp.all true in
#check @liftWrites
#print axioms liftWrites
set_option pp.all true in
#check @installTaggedIo
#print axioms installTaggedIo
set_option pp.all true in
#check @tagged_pending_restore_roundtrip
#print axioms tagged_pending_restore_roundtrip
set_option pp.all true in
#check @tagged_codec_source_finalization_publishes_exact_global_mathematical_input_vector
#print axioms tagged_codec_source_finalization_publishes_exact_global_mathematical_input_vector
end ShielddSecurity.TransferTaggedCodecPublication01
