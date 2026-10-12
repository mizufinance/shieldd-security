import ShielddSecurity.TransferScalarMontgomeryValue01
import ShielddSecurity.TransferNativeOnlyPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferTypedScalarPublication01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending restore)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject nativeSupported nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request allInputs)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
/-! Typed four-word action inputs derive canonical range from the exact finite
source-shaped scalar serializer. The ordered whole-block source input vector
is exactly the mapped mathematical Montgomery values; ordinary native-only
pending/seal/publication preserves that same vector through accepted inputs,
application root and physical recovered boundary. No canonical input bound is
supplied. Actual action-to-typed-word source projection, Rust scalar/codec/
trace/Clone/field/ownership/snapshot/ICS23/OS bindings remain explicit;
this is conditional source-model composition, not native certification. -/

theorem typed_action_projection_derives_canonical_native_input_bounds {O E K X Tree A : Type}
    (requests : List (Request O E K X Tree A))
    (typedInputs : Request O E K X Tree A → List (Vector UInt64 4))
    (sourceProjection : ∀ request ∈ requests,
      request.config.inputs request.action = (typedInputs request).map scalarKey) :
    ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus := by
  intro request present key inside
  rw [sourceProjection request present] at inside
  obtain ⟨words, _, projected⟩ := List.mem_map.mp inside
  rw [← projected]
  exact TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical words

theorem global_source_input_vector_is_exact_typed_montgomery_projection {O E K X Tree A : Type}
    (requests : List (Request O E K X Tree A))
    (typedInputs : Request O E K X Tree A → List (Vector UInt64 4))
    (sourceProjection : ∀ request ∈ requests,
      request.config.inputs request.action = (typedInputs request).map scalarKey) :
    allInputs requests = (requests.flatMap typedInputs).map montgomeryValue := by
  induction requests with
  | nil => rfl
  | cons request rest ih =>
    change request.config.inputs request.action ++ allInputs rest =
      (typedInputs request ++ rest.flatMap typedInputs).map montgomeryValue
    rw [List.map_append, sourceProjection request List.mem_cons_self]
    have values : (typedInputs request).map scalarKey = (typedInputs request).map montgomeryValue :=
      List.map_congr_left (fun words _ =>
        TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value words)
    rw [values, ih (fun r inside => sourceProjection r (List.mem_cons_of_mem request inside))]

theorem whole_typed_scalar_default_block_publishes_exact_global_montgomery_values {O E K X Tree A : Type}
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
    (io : TransferEndToEnd01.Io (ExtendedObject O) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject O))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (projectedKeys : io.ending.project = project)
    (typedGetter : io.ending.decodePending (.inl (encodeNative (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests)))
    (finalization : (TransferHostEndBlock01.finalized io.ending host height final.2).state.objects (io.ending.project TransferNullifierObjectKeys01.nullifierBytes) =
      (TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.ending.project host.active).objects (io.ending.project TransferNullifierObjectKeys01.nullifierBytes))
    (success : (TransferEndToEnd01.execute io host height final.2).root = some root) :
    allInputs requests = (requests.flatMap typedInputs).map montgomeryValue ∧
    ∃ state,
      (TransferHostEndBlock01.transferred io.ending host height final.2).returned = some state ∧
      state.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (.inl (encodeNative (.sealed (allInputs requests)))) ∧
      (allInputs requests).Nodup ∧ (allInputs requests).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs requests, key < nullifierModulus) ∧
      ∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted = allInputs requests ∧ frozen.next.applicationRoot = some root ∧
        (TransferEndToEnd01.execute io host height final.2).host.writer = .ready frozen.next ∧
        (TransferEndToEnd01.execute io host height final.2).host.phase = .idle ∧
        (TransferEndToEnd01.execute io host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
        (TransferEndToEnd01.execute io host height final.2).host.store.boundary = some frozen.next.nullifiers := by
  have nativeInputs := typed_action_projection_derives_canonical_native_input_bounds requests typedInputs sourceProjection
  exact ⟨global_source_input_vector_is_exact_typed_montgomery_projection requests typedInputs sourceProjection,
    TransferNativeOnlyPublication01.whole_native_only_default_block_publishes_exact_global_native_sealed_inputs
      encodeNative decodeNative supportedRoundtrip project injection requests parent queued final storedNativeDefault
      nativeInputs walkedNative io host height root currentState projectedKeys typedGetter finalization success⟩

set_option pp.all true in
#check @typed_action_projection_derives_canonical_native_input_bounds
#print axioms typed_action_projection_derives_canonical_native_input_bounds
set_option pp.all true in
#check @global_source_input_vector_is_exact_typed_montgomery_projection
#print axioms global_source_input_vector_is_exact_typed_montgomery_projection
set_option pp.all true in
#check @whole_typed_scalar_default_block_publishes_exact_global_montgomery_values
#print axioms whole_typed_scalar_default_block_publishes_exact_global_montgomery_values
end ShielddSecurity.TransferTypedScalarPublication01
