import ShielddSecurity.TransferBlstArmNullifierReader01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmPublication01
open TransferStateDelta
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferCanonicalWordPending01 (WordNativePending)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferBoundedNativeCodec01 (ExtendedObject nullifierModulus)
open TransferInstalledSourcePublication01 (SourceRequest)
open TransferTaggedCodecPublication01 (OtherFinalizationWrites)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferBlstArmConstructor01 (sourceFrFromLimbs)
open TransferCanonicalSourcePublication01 (canonicalSourceFields checkedSctOrderedEntry)
attribute [local irreducible] scalarKey sourceFrFromLimbs

/-! Instantiate the source-ordered request driver with the checked complete
constructor word function. Original raw four-limb inputs determine the scalar
keys modulo q. Returned whole source-driver root success derives the sealed
original fields, exact insertion order and reached Ready/Idle physical boundary.
This theorem supplies no desired scalar value, walk, admission, output object,
accepted vector or recovery Store. SDK private producers and Rust execution,
collections, application/Host/NOMT/ICS23/lock/OS contracts remain separate;
Ready does not establish healthy, durable or externally authenticated state. -/

def sourceConstructorFields {O E K X Tree A I : Type} (inputs : A → List I)
    (rawOf : I → Vector UInt64 4) (requests : List (SourceRequest O E K X Tree A I inputs)) : List CanonicalScalar :=
  canonicalSourceFields inputs (fun input => sourceFrFromLimbs (rawOf input)) requests

def sourceOriginalInputKeys {O E K X Tree A I : Type} (inputs : A → List I)
    (rawOf : I → Vector UInt64 4) (requests : List (SourceRequest O E K X Tree A I inputs)) : List Nat :=
  requests.flatMap (fun request => (inputs request.base.action).map
    (fun input => TransferScalarWordPrimitives01.packWords (rawOf input).toList % nullifierModulus))

theorem original_constructor_fields_project_to_exact_original_raw_input_keys {O E K X Tree A I : Type}
    (inputs : A → List I) (rawOf : I → Vector UInt64 4)
    (requests : List (SourceRequest O E K X Tree A I inputs)) :
    (sourceConstructorFields inputs rawOf requests).map (fun field => scalarKey field.words) =
      sourceOriginalInputKeys inputs rawOf requests := by
  induction requests with
  | nil => rfl
  | cons request rest ih =>
      change (((inputs request.base.action).map (fun input => sourceFrFromLimbs (rawOf input))) ++
          sourceConstructorFields inputs rawOf rest).map (fun field => scalarKey field.words) =
        (inputs request.base.action).map (fun input => TransferScalarWordPrimitives01.packWords (rawOf input).toList % nullifierModulus) ++
          sourceOriginalInputKeys inputs rawOf rest
      rw [List.map_append, ih, List.map_map]
      simp only [Function.comp_def, TransferBlstArmStage01.actual_constructor_input_projects_to_original_input_key_modulo_field]

theorem every_original_constructor_field_reaches_the_original_commonware_caller_as_its_input_field_bytes
    (raw : Vector UInt64 4) (scalarScratch : Vector UInt64 4)
    (scalarBytes outputBytes : Vector UInt8 32) (index : Fin 32) :
    (TransferBlstArmCaller01.sourceAsSlice
      ((sourceFrFromLimbs raw).words,scalarBytes,outputBytes) scalarScratch).2.2[index.val] =
      TransferCommonwareMapBytes01.canonicalBEByte
        (TransferScalarWordPrimitives01.packWords raw.toList : ZMod nullifierModulus) index := by
  exact TransferBlstArmConstructor01.original_locked_constructor_and_original_as_slice_caller_derive_every_original_input_field_byte
    raw scalarBytes outputBytes scalarScratch index

theorem returned_source_ordered_constructor_driver_retains_original_fields_exact_delivery_and_recovery_boundary
    {Other E K X Tree A I : Type} (inputs : A → List I) (rawOf : I → Vector UInt64 4)
    (requests : List (SourceRequest (ExtendedObject (WordTaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (WordTaggedObject Other)))
    (queued : List A)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (WordTaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (WordTaggedObject Other)) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject (WordTaggedObject Other))) (height : Fin (2 ^ 64))
    (outcome : TransferEndToEnd01.Outcome (ExtendedObject (WordTaggedObject Other)) A) (root : Nat)
    (returned : TransferWordSourceDriver01.runCompleteBlock inputs (fun input => (sourceFrFromLimbs (rawOf input)).words)
      requests verifiable nonverifiable otherObjects queued writesOf baseIo host height = some outcome)
    (success : outcome.root = some root) :
    (sourceOriginalInputKeys inputs rawOf requests).Nodup ∧
      (sourceOriginalInputKeys inputs rawOf requests).length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
      ∃ (state : State (ExtendedObject (WordTaggedObject Other))) (frozen : TransferWriterPrepareSource01.Frozen),
        state.objects (TransferInjectiveKeyPublication01.keyCode TransferNullifierObjectKeys01.nullifierBytes) =
          some (.inl (.inl (WordNativePending.sealed (sourceConstructorFields inputs rawOf requests)))) ∧
        checkedSctOrderedEntry (state.objects (TransferInjectiveKeyPublication01.keyCode TransferNullifierObjectKeys01.nullifierBytes)) =
          .ok (sourceConstructorFields inputs rawOf requests) ∧
        frozen.insertions.accepted = sourceOriginalInputKeys inputs rawOf requests ∧
        frozen.next.applicationRoot = some root ∧ outcome.host.writer = .ready frozen.next ∧
        outcome.host.phase = .idle ∧ outcome.host.store.actualRoots = frozen.next.nullifiers.roots ∧
        outcome.host.store.boundary = some frozen.next.nullifiers := by
  obtain ⟨_, state, frozen, _, _, keys, object, ordered, _, unique, capacity, _, accepted,
      appRoot, ready, idle, roots, boundary⟩ :=
    TransferCanonicalSourcePublication01.returned_whole_canonical_source_driver_publishes_original_fields_checked_getter_and_exact_boundary
      inputs (fun input => sourceFrFromLimbs (rawOf input)) requests verifiable nonverifiable otherObjects queued
      writesOf baseIo host height outcome root returned success
  have projected := original_constructor_fields_project_to_exact_original_raw_input_keys inputs rawOf requests
  have originalKeys : TransferBlockPendingSequence01.allInputs
      (TransferInstalledSourcePublication01.installRequests inputs (fun input => (sourceFrFromLimbs (rawOf input)).words) requests) =
      sourceOriginalInputKeys inputs rawOf requests := keys.trans projected
  rw [originalKeys] at unique capacity
  exact ⟨unique, capacity, state, frozen, object, ordered, accepted.trans projected,
    appRoot, ready, idle, roots, boundary⟩
set_option pp.all true in
#check @sourceConstructorFields
#print axioms sourceConstructorFields
set_option pp.all true in
#check @sourceOriginalInputKeys
#print axioms sourceOriginalInputKeys
set_option pp.all true in
#check @original_constructor_fields_project_to_exact_original_raw_input_keys
#print axioms original_constructor_fields_project_to_exact_original_raw_input_keys
set_option pp.all true in
#check @every_original_constructor_field_reaches_the_original_commonware_caller_as_its_input_field_bytes
#print axioms every_original_constructor_field_reaches_the_original_commonware_caller_as_its_input_field_bytes
set_option pp.all true in
#check @returned_source_ordered_constructor_driver_retains_original_fields_exact_delivery_and_recovery_boundary
#print axioms returned_source_ordered_constructor_driver_retains_original_fields_exact_delivery_and_recovery_boundary
end ShielddSecurity.TransferBlstArmPublication01
