import ShielddSecurity.TransferCanonicalSourceWordRetention01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCanonicalSourcePublication01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
attribute [local irreducible] TransferScalarCanonicalKey01.canonicalScalarForKey
open TransferStateDelta
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferCanonicalWordPending01 (WordNativePending encodeWordPending encodeWordScalar)
open TransferWordObjectCodec01 (WordTaggedObject encodeNative)
open TransferBoundedNativeCodec01 (ExtendedObject nullifierModulus)
open TransferInstalledSourcePublication01 (SourceRequest installRequests)
open TransferBlockPendingSequence01 (allInputs)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferTaggedCodecPublication01 (OtherFinalizationWrites)
open TransferInjectiveKeyPublication01 (keyCode)
open TransferWordSourceDriver01 (runCompleteBlock installSourceOrderedTaggedIo)
/-! Successful constructed whole-block execution retains the original ordered
canonical typed source fields in the reached sealed object and checked SCT
ordered getter. No caller walk, desired final state, codec inverse, canonical
bound, frame or getter-success premise is supplied. Canonical input type owns
packed raw <p; native private Scalar invariant, selectors, Any/Clone/imbl,
compiler, complete source trace, ownership and OS correspondence remain OPEN.
This composes source models; zero native/control/certification credit. -/

def canonicalSourceFields {O E K X Tree A I : Type} (inputs : A → List I)
    (scalarOf : I → CanonicalScalar) (requests : List (SourceRequest O E K X Tree A I inputs)) : List CanonicalScalar :=
  requests.flatMap (fun request => (inputs request.base.action).map scalarOf)

def checkedSctOrderedEntry {Other : Type} : Option (ExtendedObject (WordTaggedObject Other)) → Except Unit (List CanonicalScalar)
  | none => .ok []
  | some (.inl object) => TransferWordSctPendingRead01.sourceOrdered (some object)
  | some (.inr _) => .error ()

theorem installed_canonical_inputs_are_exact_ordered_original_field_keys {O E K X Tree A I : Type}
    (inputs : A → List I) (scalarOf : I → CanonicalScalar)
    (requests : List (SourceRequest O E K X Tree A I inputs)) :
    allInputs (installRequests inputs (fun input => (scalarOf input).words) requests) =
      (canonicalSourceFields inputs scalarOf requests).map (fun scalar => scalarKey scalar.words) := by
  induction requests with
  | nil => rfl
  | cons request rest ih =>
    change (inputs request.base.action).map (fun input => scalarKey (scalarOf input).words) ++
        allInputs (installRequests inputs (fun input => (scalarOf input).words) rest) =
      ((inputs request.base.action).map scalarOf ++ canonicalSourceFields inputs scalarOf rest).map
        (fun scalar => scalarKey scalar.words)
    rw [List.map_append, ← ih, List.map_map]
    rfl

theorem constructed_sealed_codec_retains_exact_original_canonical_source_fields {O E K X Tree A I : Type}
    (inputs : A → List I) (scalarOf : I → CanonicalScalar)
    (requests : List (SourceRequest O E K X Tree A I inputs)) :
    encodeWordPending (.sealed (allInputs (installRequests inputs (fun input => (scalarOf input).words) requests))) =
      WordNativePending.sealed (canonicalSourceFields inputs scalarOf requests) := by
  change WordNativePending.sealed ((allInputs (installRequests inputs (fun input => (scalarOf input).words) requests)).map encodeWordScalar) = _
  exact congrArg WordNativePending.sealed
    ((congrArg (fun keys : List Nat => keys.map encodeWordScalar)
      (installed_canonical_inputs_are_exact_ordered_original_field_keys inputs scalarOf requests)).trans
      (TransferCanonicalSourceWordRetention01.canonical_source_scalar_list_recovers_exact_ordered_original_fields
        (canonicalSourceFields inputs scalarOf requests)))

theorem returned_whole_canonical_source_driver_publishes_original_fields_checked_getter_and_exact_boundary {Other E K X Tree A I : Type}
    (inputs : A → List I) (scalarOf : I → CanonicalScalar)
    (sourceRequests : List (SourceRequest (ExtendedObject (WordTaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (WordTaggedObject Other))) (queued : List A)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (WordTaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (WordTaggedObject Other)) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject (WordTaggedObject Other))) (height : Fin (2 ^ 64))
    (outcome : TransferEndToEnd01.Outcome (ExtendedObject (WordTaggedObject Other)) A) (root : Nat)
    (returned : runCompleteBlock inputs (fun input => (scalarOf input).words) sourceRequests verifiable nonverifiable otherObjects queued writesOf baseIo host height = some outcome)
    (success : outcome.root = some root) :
    ∃ (final : State (ExtendedObject (WordTaggedObject Other)) × List A)
      (state : State (ExtendedObject (WordTaggedObject Other))) (frozen : TransferWriterPrepareSource01.Frozen),
      outcome = TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) {host with active := final.1} height final.2 ∧
      (TransferHostEndBlock01.transferred (installSourceOrderedTaggedIo writesOf baseIo).ending {host with active := final.1} height final.2).returned = some state ∧
      allInputs (installRequests inputs (fun input => (scalarOf input).words) sourceRequests) =
        (canonicalSourceFields inputs scalarOf sourceRequests).map (fun scalar => scalarKey scalar.words) ∧
      state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) =
        some (.inl (.inl (WordNativePending.sealed (canonicalSourceFields inputs scalarOf sourceRequests)))) ∧
      checkedSctOrderedEntry (state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes)) =
        .ok (canonicalSourceFields inputs scalarOf sourceRequests) ∧
      TransferCheckedWordPublication01.checkedNativeEntry (state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes)) =
        .ok (.sealed (allInputs (installRequests inputs (fun input => (scalarOf input).words) sourceRequests))) ∧
      (allInputs (installRequests inputs (fun input => (scalarOf input).words) sourceRequests)).Nodup ∧
      (allInputs (installRequests inputs (fun input => (scalarOf input).words) sourceRequests)).length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
      (∀ key ∈ allInputs (installRequests inputs (fun input => (scalarOf input).words) sourceRequests), key < nullifierModulus) ∧
      frozen.insertions.accepted = (canonicalSourceFields inputs scalarOf sourceRequests).map (fun scalar => scalarKey scalar.words) ∧
      frozen.next.applicationRoot = some root ∧ outcome.host.writer = .ready frozen.next ∧ outcome.host.phase = .idle ∧
      outcome.host.store.actualRoots = frozen.next.nullifiers.roots ∧ outcome.host.store.boundary = some frozen.next.nullifiers := by
  obtain ⟨final, state, frozen, reached, transferred, _, object, checked, unique, capacity, canonical,
      accepted, appRoot, ready, idle, roots, boundary⟩ :=
    TransferCheckedWordPublication01.returned_whole_word_driver_derives_successful_checked_getter_and_exact_boundary
      inputs (fun input => (scalarOf input).words) sourceRequests verifiable nonverifiable otherObjects queued writesOf baseIo host height outcome root returned success
  have keys := installed_canonical_inputs_are_exact_ordered_original_field_keys inputs scalarOf sourceRequests
  have fields := constructed_sealed_codec_retains_exact_original_canonical_source_fields inputs scalarOf sourceRequests
  have stored : state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (.inl (WordNativePending.sealed (canonicalSourceFields inputs scalarOf sourceRequests)))) :=
    object.trans (congrArg (fun pending : WordNativePending =>
      (some (.inl (.inl pending)) : Option (ExtendedObject (WordTaggedObject Other)))) fields)
  have ordered : checkedSctOrderedEntry (state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes)) =
      .ok (canonicalSourceFields inputs scalarOf sourceRequests) := by
    rw [stored]
    rfl
  exact ⟨final, state, frozen, reached, transferred, keys, stored, ordered, checked, unique, capacity,
    canonical, accepted.trans keys, appRoot, ready, idle, roots, boundary⟩

set_option pp.all true in
#check @canonicalSourceFields
#print axioms canonicalSourceFields
set_option pp.all true in
#check @checkedSctOrderedEntry
#print axioms checkedSctOrderedEntry
set_option pp.all true in
#check @installed_canonical_inputs_are_exact_ordered_original_field_keys
#print axioms installed_canonical_inputs_are_exact_ordered_original_field_keys
set_option pp.all true in
#check @constructed_sealed_codec_retains_exact_original_canonical_source_fields
#print axioms constructed_sealed_codec_retains_exact_original_canonical_source_fields
set_option pp.all true in
#check @returned_whole_canonical_source_driver_publishes_original_fields_checked_getter_and_exact_boundary
#print axioms returned_whole_canonical_source_driver_publishes_original_fields_checked_getter_and_exact_boundary
end ShielddSecurity.TransferCanonicalSourcePublication01
