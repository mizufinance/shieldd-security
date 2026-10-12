import ShielddSecurity.TransferInjectiveKeyPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferFixedFinalizerPublication01
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
/-! Fixed known post-seal object mutation recipe: delete block materialization,
replace cached tree with an actual native object, delete three compliance
buffers, then delete routing buffer. No caller mutation list/permitted-key
proof supplied. Source call ordering association is static, not an exhaustive
native trace refinement. Native component/hidden callee/tree/value/input/
codec/cache/ownership/OS correspondences remain distinct. -/

structure FinalizationWrites (O E A : Type) where
  nativeTreeObject : O
  verifiable : Writes Bytes
  nonverifiable : Writes Bytes
  events : List E
  queued : List A

def fixedMutations {O : Type} (nativeTreeObject : O) : List (Mutation (ExtendedObject O)) :=
  [⟨[115, 99, 116, 47, 99, 97, 99, 104, 101, 47, 98, 108, 111, 99, 107, 95, 109, 97, 116, 101, 114, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110], by decide, none⟩,
   ⟨[115, 99, 116, 47, 99, 97, 99, 104, 101, 47, 99, 97, 99, 104, 101, 100, 95, 115, 116, 97, 116, 101, 95, 99, 111, 109, 109, 105, 116, 109, 101, 110, 116, 95, 116, 114, 101, 101], by decide, some (.inl nativeTreeObject)⟩,
   ⟨[99, 111, 109, 112, 97, 99, 116, 98, 108, 111, 99, 107, 47, 112, 101, 110, 100, 105, 110, 103, 95, 114, 111, 117, 116, 105, 110, 103, 95, 97, 99, 116, 105, 111, 110, 115], by decide, none⟩,
   ⟨[99, 111, 109, 112, 108, 105, 97, 110, 99, 101, 47, 112, 101, 110, 100, 105, 110, 103, 95, 117, 115, 101, 114, 95, 114, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 115], by decide, none⟩,
   ⟨[99, 111, 109, 112, 108, 105, 97, 110, 99, 101, 47, 112, 101, 110, 100, 105, 110, 103, 95, 117, 115, 101, 114, 95, 115, 116, 97, 116, 117, 115, 95, 99, 104, 97, 110, 103, 101, 115], by decide, none⟩,
   ⟨[99, 111, 109, 112, 108, 105, 97, 110, 99, 101, 47, 112, 101, 110, 100, 105, 110, 103, 95, 97, 115, 115, 101, 116, 95, 114, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 115], by decide, none⟩]

def toEffects {O E A : Type} (writes : FinalizationWrites O E A) : Effects (ExtendedObject O) E A :=
  ⟨fixedMutations writes.nativeTreeObject, writes.verifiable, writes.nonverifiable, writes.events, writes.queued⟩

def installFixedIo {O E A : Type} (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → FinalizationWrites O E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject O) E A) : TransferEndToEnd01.Io (ExtendedObject O) E A :=
  installIo encodeNative decodeNative keyCode (fun height state queued => toEffects (writesOf height state queued)) baseIo

theorem fixed_mutation_recipe_has_exact_source_key_order {O : Type} (tree : O) :
    (fixedMutations tree).map (fun mutation => mutation.key) = [[115, 99, 116, 47, 99, 97, 99, 104, 101, 47, 98, 108, 111, 99, 107, 95, 109, 97, 116, 101, 114, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110], [115, 99, 116, 47, 99, 97, 99, 104, 101, 47, 99, 97, 99, 104, 101, 100, 95, 115, 116, 97, 116, 101, 95, 99, 111, 109, 109, 105, 116, 109, 101, 110, 116, 95, 116, 114, 101, 101], [99, 111, 109, 112, 97, 99, 116, 98, 108, 111, 99, 107, 47, 112, 101, 110, 100, 105, 110, 103, 95, 114, 111, 117, 116, 105, 110, 103, 95, 97, 99, 116, 105, 111, 110, 115], [99, 111, 109, 112, 108, 105, 97, 110, 99, 101, 47, 112, 101, 110, 100, 105, 110, 103, 95, 117, 115, 101, 114, 95, 114, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 115], [99, 111, 109, 112, 108, 105, 97, 110, 99, 101, 47, 112, 101, 110, 100, 105, 110, 103, 95, 117, 115, 101, 114, 95, 115, 116, 97, 116, 117, 115, 95, 99, 104, 97, 110, 103, 101, 115], [99, 111, 109, 112, 108, 105, 97, 110, 99, 101, 47, 112, 101, 110, 100, 105, 110, 103, 95, 97, 115, 115, 101, 116, 95, 114, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 115]] := rfl

theorem fixed_mutation_recipe_has_six_operations {O : Type} (tree : O) :
    (fixedMutations tree).length = 6 := rfl

theorem fixed_mutation_recipe_has_exact_put_and_deletion_tombstone_order {O : Type} (tree : O) :
    (fixedMutations tree).map (fun mutation => mutation.value.isSome) = [false, true, false, false, false, false] := rfl

theorem fixed_known_source_finalization_publishes_exact_global_mathematical_input_vector {O E K X Tree A I : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject O) E K X Tree A I inputs))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (storedNativeDefault : parent.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (encodeNative (.opened [] []))))
    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent queued (installRequests inputs wordOf sourceRequests) = some final)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → FinalizationWrites O E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject O) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject O))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (typedGetter : (installFixedIo encodeNative decodeNative writesOf baseIo).ending.decodePending (.inl (encodeNative (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) = restore (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))
    (success : (TransferEndToEnd01.execute (installFixedIo encodeNative decodeNative writesOf baseIo) host height final.2).root = some root) :
    allInputs (installRequests inputs wordOf sourceRequests) = (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
    ∃ state,
      (TransferHostEndBlock01.transferred (installFixedIo encodeNative decodeNative writesOf baseIo).ending host height final.2).returned = some state ∧
      state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = some (.inl (encodeNative (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) ∧
      (allInputs (installRequests inputs wordOf sourceRequests)).Nodup ∧ (allInputs (installRequests inputs wordOf sourceRequests)).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs (installRequests inputs wordOf sourceRequests), key < nullifierModulus) ∧
      ∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted = allInputs (installRequests inputs wordOf sourceRequests) ∧ frozen.next.applicationRoot = some root ∧
        (TransferEndToEnd01.execute (installFixedIo encodeNative decodeNative writesOf baseIo) host height final.2).host.writer = .ready frozen.next ∧
        (TransferEndToEnd01.execute (installFixedIo encodeNative decodeNative writesOf baseIo) host height final.2).host.phase = .idle ∧
        (TransferEndToEnd01.execute (installFixedIo encodeNative decodeNative writesOf baseIo) host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
        (TransferEndToEnd01.execute (installFixedIo encodeNative decodeNative writesOf baseIo) host height final.2).host.store.boundary = some frozen.next.nullifiers := by
  exact TransferInjectiveKeyPublication01.injective_labeled_source_and_finalizer_publish_exact_global_mathematical_input_vector
    encodeNative decodeNative supportedRoundtrip inputs wordOf sourceRequests parent queued final storedNativeDefault
    walkedNative (fun height state queued => toEffects (writesOf height state queued)) baseIo host height root currentState typedGetter success
set_option pp.all true in
#check @FinalizationWrites
#print axioms FinalizationWrites
set_option pp.all true in
#check @fixedMutations
#print axioms fixedMutations
set_option pp.all true in
#check @toEffects
#print axioms toEffects
set_option pp.all true in
#check @installFixedIo
#print axioms installFixedIo
set_option pp.all true in
#check @fixed_mutation_recipe_has_exact_source_key_order
#print axioms fixed_mutation_recipe_has_exact_source_key_order
set_option pp.all true in
#check @fixed_mutation_recipe_has_six_operations
#print axioms fixed_mutation_recipe_has_six_operations
set_option pp.all true in
#check @fixed_mutation_recipe_has_exact_put_and_deletion_tombstone_order
#print axioms fixed_mutation_recipe_has_exact_put_and_deletion_tombstone_order
set_option pp.all true in
#check @fixed_known_source_finalization_publishes_exact_global_mathematical_input_vector
#print axioms fixed_known_source_finalization_publishes_exact_global_mathematical_input_vector
end ShielddSecurity.TransferFixedFinalizerPublication01
