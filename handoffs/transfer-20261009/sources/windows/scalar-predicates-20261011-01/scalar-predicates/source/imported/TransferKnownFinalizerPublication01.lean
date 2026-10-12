import ShielddSecurity.TransferFinalizationObjectFrames01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferKnownFinalizerPublication01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending restore)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject nativeSupported nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request allInputs)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferFinalizationObjectFrames01 (Mutation mutationWalk)
/-! Concrete source model finalizer seals, executes six-key object mutations,
overlays V/NV writes and returns observed queue/events. Installation derives
pending retention; publication no longer takes a desired pending field frame.
Effects may vary with actual height/sealed state/queue. Their allowed object
keys restrict this model to six known keys, not an exhaustive native trace.
Rust trace completeness/order/value/selector/codec/cache and every other native
correspondence remain separate; no native/control/certification credit. -/

structure Effects (O E A : Type) where
  mutations : List (Mutation O)
  verifiable : Writes Bytes
  nonverifiable : Writes Bytes
  events : List E
  queued : List A

def writeNonObjectEffects {O E A : Type} (delta : Delta O E) (effects : Effects O E A) : Delta O E :=
  {delta with cache := {delta.cache with verifiable := mergeWrites delta.cache.verifiable effects.verifiable, nonverifiable := mergeWrites delta.cache.nonverifiable effects.nonverifiable, events := delta.cache.events ++ effects.events}}

def finishKnown {O E A : Type} (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (project : Bytes → Nat)
    (effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)
    (height : Fin (2 ^ 64)) (state : State (ExtendedObject O)) (queued : List A) :
    TransferHostEndBlock01.ApplicationResult (ExtendedObject O) E A :=
  let sealed := TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
    (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state
  let effects := effectsOf height sealed queued
  let after := writeNonObjectEffects (mutationWalk project ⟨sealed, (empty : Cache (ExtendedObject O) E)⟩ effects.mutations) effects
  ⟨applyCache after.parent after.cache, effects.queued, after.cache.events⟩

def installIo {O E A : Type} (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (project : Bytes → Nat)
    (effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)
    (io : TransferEndToEnd01.Io (ExtendedObject O) E A) : TransferEndToEnd01.Io (ExtendedObject O) E A :=
  {io with ending := {io.ending with endApplication := finishKnown encodeNative decodeNative project effectsOf, project := project}}

theorem concrete_known_finalizer_derives_pending_retention {O E A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)
    (height : Fin (2 ^ 64)) (state : State (ExtendedObject O)) (queued : List A) :
    (finishKnown encodeNative decodeNative project effectsOf height state queued).state.objects
      (project TransferNullifierObjectKeys01.nullifierBytes) =
      (TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state).objects
      (project TransferNullifierObjectKeys01.nullifierBytes) := by
  let sealed := TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
    (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state
  let effects := effectsOf height sealed queued
  change (applyCache (mutationWalk project ⟨sealed, (empty : Cache (ExtendedObject O) E)⟩ effects.mutations).parent
    (mutationWalk project ⟨sealed, (empty : Cache (ExtendedObject O) E)⟩ effects.mutations).cache).objects
      (project TransferNullifierObjectKeys01.nullifierBytes) = sealed.objects (project TransferNullifierObjectKeys01.nullifierBytes)
  exact TransferFinalizationObjectFrames01.symbolic_known_finalization_mutation_walk_preserves_pending_observation
    project injection ⟨sealed, (empty : Cache (ExtendedObject O) E)⟩ effects.mutations

theorem installed_known_finalizer_derives_reached_publication_field_frame {O E A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)
    (io : TransferEndToEnd01.Io (ExtendedObject O) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject O)) (height : Fin (2 ^ 64)) (queued : List A) :
    (TransferHostEndBlock01.finalized (installIo encodeNative decodeNative project effectsOf io).ending host height queued).state.objects
      (project TransferNullifierObjectKeys01.nullifierBytes) =
      (TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project host.active).objects
      (project TransferNullifierObjectKeys01.nullifierBytes) :=
  concrete_known_finalizer_derives_pending_retention encodeNative decodeNative project injection effectsOf height host.active queued

theorem concrete_known_finalizer_publishes_exact_global_typed_montgomery_values {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (requests : List (Request (ExtendedObject O) E K X Tree A))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (storedNativeDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (encodeNative (.opened [] []))))
    (typedInputs : Request (ExtendedObject O) E K X Tree A → List (Vector UInt64 4))
    (sourceProjection : ∀ request ∈ requests,
      request.config.inputs request.action = (typedInputs request).map scalarKey)
    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final)
    (effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject O) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject O))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (typedGetter : (installIo encodeNative decodeNative project effectsOf baseIo).ending.decodePending (.inl (encodeNative (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests)))
    (success : (TransferEndToEnd01.execute (installIo encodeNative decodeNative project effectsOf baseIo) host height final.2).root = some root) :
    allInputs requests = (requests.flatMap typedInputs).map montgomeryValue ∧
    ∃ state,
      (TransferHostEndBlock01.transferred (installIo encodeNative decodeNative project effectsOf baseIo).ending host height final.2).returned = some state ∧
      state.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (.inl (encodeNative (.sealed (allInputs requests)))) ∧
      (allInputs requests).Nodup ∧ (allInputs requests).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs requests, key < nullifierModulus) ∧
      ∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted = allInputs requests ∧ frozen.next.applicationRoot = some root ∧
        (TransferEndToEnd01.execute (installIo encodeNative decodeNative project effectsOf baseIo) host height final.2).host.writer = .ready frozen.next ∧
        (TransferEndToEnd01.execute (installIo encodeNative decodeNative project effectsOf baseIo) host height final.2).host.phase = .idle ∧
        (TransferEndToEnd01.execute (installIo encodeNative decodeNative project effectsOf baseIo) host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
        (TransferEndToEnd01.execute (installIo encodeNative decodeNative project effectsOf baseIo) host height final.2).host.store.boundary = some frozen.next.nullifiers := by
  let io := installIo encodeNative decodeNative project effectsOf baseIo
  exact TransferTypedScalarPublication01.whole_typed_scalar_default_block_publishes_exact_global_montgomery_values
    encodeNative decodeNative supportedRoundtrip project injection requests parent queued final storedNativeDefault
    typedInputs sourceProjection walkedNative io host height root currentState rfl typedGetter
    (installed_known_finalizer_derives_reached_publication_field_frame encodeNative decodeNative project injection effectsOf baseIo host height final.2)
    success
set_option pp.all true in
#check @Effects
#print axioms Effects
set_option pp.all true in
#check @writeNonObjectEffects
#print axioms writeNonObjectEffects
set_option pp.all true in
#check @finishKnown
#print axioms finishKnown
set_option pp.all true in
#check @installIo
#print axioms installIo
set_option pp.all true in
#check @concrete_known_finalizer_derives_pending_retention
#print axioms concrete_known_finalizer_derives_pending_retention
set_option pp.all true in
#check @installed_known_finalizer_derives_reached_publication_field_frame
#print axioms installed_known_finalizer_derives_reached_publication_field_frame
set_option pp.all true in
#check @concrete_known_finalizer_publishes_exact_global_typed_montgomery_values
#print axioms concrete_known_finalizer_publishes_exact_global_typed_montgomery_values
end ShielddSecurity.TransferKnownFinalizerPublication01
