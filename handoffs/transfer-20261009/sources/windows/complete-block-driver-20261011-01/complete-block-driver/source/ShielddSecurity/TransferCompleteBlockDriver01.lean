import ShielddSecurity.TransferAbsentStartPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCompleteBlockDriver01
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
open TransferTaggedCodecPublication01 (TaggedObject encodePending decodePending OtherFinalizationWrites liftWrites installTaggedIo)
open TransferBlockPendingSequence01 (step walk)
open TransferAbsentStartPublication01 (freshParent)
/-! Returned whole-block source model explicitly composes native-only action
walk from fresh absent pending cache, assigns its reached state to the Host,
then executes concrete tagged-codec/fixed-finalizer publication. A returned
root derives the actual walk/reached state and complete publication witness;
caller walk-result and host-current-state equalities are eliminated.
None means no modeled whole return, with no failure-prefix/rollback claim.
Native loop/Host ownership/fresh cache/selectors/full component trace/library/
snapshot/OS correspondence remains explicit; zero native/certification credit. -/

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
    (fun final => TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) {host with active := final.1} height final.2)

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
      outcome = TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) {host with active := final.1} height final.2 ∧
      allInputs (installRequests inputs wordOf sourceRequests) =
        (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
      ∃ state,
        (TransferHostEndBlock01.transferred (installTaggedIo writesOf baseIo).ending {host with active := final.1} height final.2).returned = some state ∧
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
    have same : TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) {host with active := final.1} height final.2 = outcome :=
      Option.some.inj (by simpa only [runCompleteBlock, ran, Option.map_some] using returned)
    have rootSuccess : (TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) {host with active := final.1} height final.2).root = some root := by
      rw [same]
      exact success
    have publication := TransferAbsentStartPublication01.fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector
      inputs wordOf sourceRequests verifiable nonverifiable otherObjects queued final ran writesOf baseIo
      {host with active := final.1} height root rfl rootSuccess
    refine ⟨final, rfl, same.symm, ?_⟩
    simpa only [same] using publication

set_option pp.all true in
#check @runCompleteBlock
#print axioms runCompleteBlock
set_option pp.all true in
#check @returned_whole_block_derives_actual_walk_exact_inputs_and_publication
#print axioms returned_whole_block_derives_actual_walk_exact_inputs_and_publication
end ShielddSecurity.TransferCompleteBlockDriver01
