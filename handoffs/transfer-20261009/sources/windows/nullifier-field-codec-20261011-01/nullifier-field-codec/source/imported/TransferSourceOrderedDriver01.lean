import ShielddSecurity.TransferSourceOrderedFinalizer01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferSourceOrderedDriver01
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
open TransferTaggedCodecPublication01 (TaggedObject encodePending decodePending OtherFinalizationWrites liftWrites)
open TransferBlockPendingSequence01 (step walk)
open TransferAbsentStartPublication01 (freshParent)
/-! Corrected source-ordered known finalization is composed into concrete
tagged getter, fresh absent parent, source requests and returned whole driver.
The inherited older fixed list remains only its defined model. Full native
trace/callee/value/primitive/field/cache/snapshot/ownership/OS bindings remain
explicit. No native, control or certification credit. -/

def installSourceOrderedTaggedIo {Other E A : Type}
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (TaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A) :
    TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A :=
  TransferSourceOrderedFinalizer01.installFixedIo encodePending decodePending
    (fun height state queued => liftWrites (writesOf height state queued))
    {baseIo with ending := {baseIo.ending with decodePending := TransferPendingFiniteCodec01.decode (decodeObject decodePending)}}

theorem fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector {Other E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject (TaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (TaggedObject Other))) (queued : List A) (final : State (ExtendedObject (TaggedObject Other)) × List A)
    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodePending)
      (TransferPendingFiniteCodec01.decode (decodeObject decodePending)) keyCode (freshParent verifiable nonverifiable otherObjects) queued (installRequests inputs wordOf sourceRequests) = some final)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (TaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject (TaggedObject Other)))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (success : (TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) host height final.2).root = some root) :
    allInputs (installRequests inputs wordOf sourceRequests) = (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
    ∃ state,
      (TransferHostEndBlock01.transferred (installSourceOrderedTaggedIo writesOf baseIo).ending host height final.2).returned = some state ∧
      state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = some (.inl (encodePending (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) ∧
      (allInputs (installRequests inputs wordOf sourceRequests)).Nodup ∧ (allInputs (installRequests inputs wordOf sourceRequests)).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs (installRequests inputs wordOf sourceRequests), key < nullifierModulus) ∧
      ∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted = allInputs (installRequests inputs wordOf sourceRequests) ∧ frozen.next.applicationRoot = some root ∧
        (TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) host height final.2).host.writer = .ready frozen.next ∧
        (TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) host height final.2).host.phase = .idle ∧
        (TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
        (TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) host height final.2).host.store.boundary = some frozen.next.nullifiers := by
  let requests := installRequests inputs wordOf sourceRequests
  let parent := freshParent verifiable nonverifiable otherObjects
  let io := installSourceOrderedTaggedIo writesOf baseIo
  have sourceProjection := TransferInstalledSourcePublication01.installed_request_batch_derives_every_source_projection inputs wordOf sourceRequests
  have nativeInputs := TransferTypedScalarPublication01.typed_action_projection_derives_canonical_native_input_bounds
    requests (fun request => typedWords inputs wordOf request.action) sourceProjection
  have absent : parent.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = none := by
    simp only [parent, freshParent, ite_true]
  have getter : io.ending.decodePending (.inl (encodePending (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests)) := rfl
  have frame := TransferKnownFinalizerPublication01.installed_known_finalizer_derives_reached_publication_field_frame
    (encodePending (Other := Other)) (decodePending (Other := Other)) keyCode TransferInjectiveKeyPublication01.keyCode_is_injective
    (fun height state queued => TransferSourceOrderedFinalizer01.toEffects (liftWrites (writesOf height state queued)))
    {baseIo with ending := {baseIo.ending with decodePending := TransferPendingFiniteCodec01.decode (decodeObject decodePending)}}
    host height final.2
  have values := TransferTypedScalarPublication01.global_source_input_vector_is_exact_typed_montgomery_projection
    requests (fun request => typedWords inputs wordOf request.action) sourceProjection
  refine ⟨values.trans ?_, ?_⟩
  · exact congrArg (fun words : List (Vector UInt64 4) => words.map montgomeryValue)
      (TransferInstalledSourcePublication01.installed_request_batch_retains_exact_ordered_source_word_vector inputs wordOf sourceRequests)
  · exact TransferAbsentStartPublication01.whole_absent_native_default_block_publishes_exact_global_native_sealed_inputs
      (encodePending (Other := Other)) (decodePending (Other := Other))
      (fun native _ => TransferTaggedCodecPublication01.tagged_pending_restore_roundtrip native)
      keyCode TransferInjectiveKeyPublication01.keyCode_is_injective requests parent queued final absent nativeInputs walkedNative
      io host height root currentState rfl getter frame success
def runCompleteBlock {Other E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject (TaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (TaggedObject Other))) (queued : List A)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (TaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject (TaggedObject Other))) (height : Fin (2 ^ 64)) :
    Option (TransferEndToEnd01.Outcome (ExtendedObject (TaggedObject Other)) A) :=
  (walk (TransferNativeReachableErasure01.nativeOnlyEncode encodePending)
    (TransferPendingFiniteCodec01.decode (decodeObject decodePending)) keyCode
    (freshParent verifiable nonverifiable otherObjects) queued (installRequests inputs wordOf sourceRequests)).map
    (fun final => TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) {host with active := final.1} height final.2)

theorem returned_whole_block_derives_actual_walk_exact_inputs_and_publication {Other E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject (TaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (TaggedObject Other))) (queued : List A)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (TaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject (TaggedObject Other))) (height : Fin (2 ^ 64))
    (outcome : TransferEndToEnd01.Outcome (ExtendedObject (TaggedObject Other)) A) (root : Nat)
    (returned : runCompleteBlock inputs wordOf sourceRequests verifiable nonverifiable otherObjects queued writesOf baseIo host height = some outcome)
    (success : outcome.root = some root) :
    ∃ final : State (ExtendedObject (TaggedObject Other)) × List A,
      walk (TransferNativeReachableErasure01.nativeOnlyEncode encodePending)
        (TransferPendingFiniteCodec01.decode (decodeObject decodePending)) keyCode
        (freshParent verifiable nonverifiable otherObjects) queued (installRequests inputs wordOf sourceRequests) = some final ∧
      outcome = TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) {host with active := final.1} height final.2 ∧
      allInputs (installRequests inputs wordOf sourceRequests) =
        (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
      ∃ state,
        (TransferHostEndBlock01.transferred (installSourceOrderedTaggedIo writesOf baseIo).ending {host with active := final.1} height final.2).returned = some state ∧
        state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) =
          some (.inl (encodePending (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) ∧
        (allInputs (installRequests inputs wordOf sourceRequests)).Nodup ∧
        (allInputs (installRequests inputs wordOf sourceRequests)).length ≤ blockCapacity ∧
        (∀ key ∈ allInputs (installRequests inputs wordOf sourceRequests), key < nullifierModulus) ∧
        ∃ (frozen : TransferWriterPrepareSource01.Frozen),
          frozen.insertions.accepted = allInputs (installRequests inputs wordOf sourceRequests) ∧ frozen.next.applicationRoot = some root ∧
          outcome.host.writer = .ready frozen.next ∧ outcome.host.phase = .idle ∧
          outcome.host.store.actualRoots = frozen.next.nullifiers.roots ∧ outcome.host.store.boundary = some frozen.next.nullifiers := by
  cases ran : walk (TransferNativeReachableErasure01.nativeOnlyEncode encodePending)
      (TransferPendingFiniteCodec01.decode (decodeObject decodePending)) keyCode
      (freshParent verifiable nonverifiable otherObjects) queued (installRequests inputs wordOf sourceRequests) with
  | none =>
    simp only [runCompleteBlock, ran, Option.map_none] at returned
    cases returned
  | some final =>
    have same : TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) {host with active := final.1} height final.2 = outcome :=
      Option.some.inj (by simpa only [runCompleteBlock, ran, Option.map_some] using returned)
    have rootSuccess : (TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) {host with active := final.1} height final.2).root = some root := by
      rw [same]
      exact success
    have publication := fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector
      inputs wordOf sourceRequests verifiable nonverifiable otherObjects queued final ran writesOf baseIo
      {host with active := final.1} height root rfl rootSuccess
    refine ⟨final, rfl, same.symm, ?_⟩
    simpa only [same] using publication

set_option pp.all true in
#check @installSourceOrderedTaggedIo
#print axioms installSourceOrderedTaggedIo
set_option pp.all true in
#check @fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector
#print axioms fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector
set_option pp.all true in
#check @runCompleteBlock
#print axioms runCompleteBlock
set_option pp.all true in
#check @returned_whole_block_derives_actual_walk_exact_inputs_and_publication
#print axioms returned_whole_block_derives_actual_walk_exact_inputs_and_publication
end ShielddSecurity.TransferSourceOrderedDriver01
