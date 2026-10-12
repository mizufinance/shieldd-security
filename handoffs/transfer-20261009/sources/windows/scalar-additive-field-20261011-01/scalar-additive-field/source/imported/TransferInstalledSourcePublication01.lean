import ShielddSecurity.TransferKnownFinalizerPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferInstalledSourcePublication01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending restore)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject nativeSupported nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request allInputs)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferSourceTypedInputProjection01 (typedWords installTypedInputs)
open TransferKnownFinalizerPublication01 (Effects installIo)
/-! Concrete typed source request construction preserves every actual input
slot/order and derives the configuration projection. Native input selectors
and source nonemptiness are explicit. Whole publication supplies neither
desired source-key equality, canonical bounds, nor finalization field frame.
Full native input/Scalar/iterator/proof/codec/six-key trace completeness/cache/
ownership/OS correspondences remain separate. Source-model composition only. -/

structure SourceRequest (O E K X Tree A I : Type) (inputs : A → List I) where
  base : Request O E K X Tree A
  sourceNonempty : (inputs base.action).isEmpty = false

def installRequest {O E K X Tree A I : Type} (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (request : SourceRequest O E K X Tree A I inputs) : Request O E K X Tree A :=
  {request.base with config := installTypedInputs request.base.config inputs wordOf, supported := request.base.supported, nonempty := (List.isEmpty_map (l := inputs request.base.action) (f := fun input => scalarKey (wordOf input))).trans request.sourceNonempty}

def installRequests {O E K X Tree A I : Type} (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (requests : List (SourceRequest O E K X Tree A I inputs)) : List (Request O E K X Tree A) :=
  requests.map (installRequest inputs wordOf)

theorem installed_request_derives_exact_typed_input_projection {O E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4) (request : SourceRequest O E K X Tree A I inputs) :
    (installRequest inputs wordOf request).config.inputs (installRequest inputs wordOf request).action =
      (typedWords inputs wordOf (installRequest inputs wordOf request).action).map scalarKey :=
  TransferSourceTypedInputProjection01.installed_config_inputs_are_exact_ordered_typed_scalar_projection
    request.base.config inputs wordOf request.base.action

theorem installed_request_batch_derives_every_source_projection {O E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4) (requests : List (SourceRequest O E K X Tree A I inputs)) :
    ∀ request ∈ installRequests inputs wordOf requests,
      request.config.inputs request.action = (typedWords inputs wordOf request.action).map scalarKey := by
  intro request present
  obtain ⟨original, _, same⟩ := List.mem_map.mp present
  subst request
  exact installed_request_derives_exact_typed_input_projection inputs wordOf original

theorem installed_request_batch_retains_exact_ordered_source_word_vector {O E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4) (requests : List (SourceRequest O E K X Tree A I inputs)) :
    (installRequests inputs wordOf requests).flatMap (fun request => typedWords inputs wordOf request.action) =
      requests.flatMap (fun request => typedWords inputs wordOf request.base.action) := by
  change (requests.map (installRequest inputs wordOf)).flatMap (fun request => typedWords inputs wordOf request.action) = _
  rw [List.flatMap_map]
  rfl

theorem installed_source_and_finalizer_publish_exact_global_mathematical_input_vector {O E K X Tree A I : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject O) E K X Tree A I inputs))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (storedNativeDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (encodeNative (.opened [] []))))
    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued (installRequests inputs wordOf sourceRequests) = some final)
    (effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject O) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject O))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (typedGetter : (installIo encodeNative decodeNative project effectsOf baseIo).ending.decodePending (.inl (encodeNative (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) = restore (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))
    (success : (TransferEndToEnd01.execute (installIo encodeNative decodeNative project effectsOf baseIo) host height final.2).root = some root) :
    allInputs (installRequests inputs wordOf sourceRequests) = (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
    ∃ state,
      (TransferHostEndBlock01.transferred (installIo encodeNative decodeNative project effectsOf baseIo).ending host height final.2).returned = some state ∧
      state.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (.inl (encodeNative (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) ∧
      (allInputs (installRequests inputs wordOf sourceRequests)).Nodup ∧ (allInputs (installRequests inputs wordOf sourceRequests)).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs (installRequests inputs wordOf sourceRequests), key < nullifierModulus) ∧
      ∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted = allInputs (installRequests inputs wordOf sourceRequests) ∧ frozen.next.applicationRoot = some root ∧
        (TransferEndToEnd01.execute (installIo encodeNative decodeNative project effectsOf baseIo) host height final.2).host.writer = .ready frozen.next ∧
        (TransferEndToEnd01.execute (installIo encodeNative decodeNative project effectsOf baseIo) host height final.2).host.phase = .idle ∧
        (TransferEndToEnd01.execute (installIo encodeNative decodeNative project effectsOf baseIo) host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
        (TransferEndToEnd01.execute (installIo encodeNative decodeNative project effectsOf baseIo) host height final.2).host.store.boundary = some frozen.next.nullifiers := by
  let requests := installRequests inputs wordOf sourceRequests
  obtain ⟨values, publication⟩ := TransferKnownFinalizerPublication01.concrete_known_finalizer_publishes_exact_global_typed_montgomery_values
    encodeNative decodeNative supportedRoundtrip project injection requests parent queued final storedNativeDefault
    (fun request => typedWords inputs wordOf request.action)
    (installed_request_batch_derives_every_source_projection inputs wordOf sourceRequests)
    walkedNative effectsOf baseIo host height root currentState typedGetter success
  refine ⟨values.trans ?_, publication⟩
  exact congrArg (fun words : List (Vector UInt64 4) => words.map montgomeryValue)
    (installed_request_batch_retains_exact_ordered_source_word_vector inputs wordOf sourceRequests)
set_option pp.all true in
#check @SourceRequest
#print axioms SourceRequest
set_option pp.all true in
#check @installRequest
#print axioms installRequest
set_option pp.all true in
#check @installRequests
#print axioms installRequests
set_option pp.all true in
#check @installed_request_derives_exact_typed_input_projection
#print axioms installed_request_derives_exact_typed_input_projection
set_option pp.all true in
#check @installed_request_batch_derives_every_source_projection
#print axioms installed_request_batch_derives_every_source_projection
set_option pp.all true in
#check @installed_request_batch_retains_exact_ordered_source_word_vector
#print axioms installed_request_batch_retains_exact_ordered_source_word_vector
set_option pp.all true in
#check @installed_source_and_finalizer_publish_exact_global_mathematical_input_vector
#print axioms installed_source_and_finalizer_publish_exact_global_mathematical_input_vector
end ShielddSecurity.TransferInstalledSourcePublication01
