import ShielddSecurity.TransferWordObjectRead01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCheckedWordPublication01
open TransferStateDelta
open TransferWordObjectCodec01 (WordTaggedObject encodeNative decodeNative)
open TransferCanonicalWordPending01 (WordNativePending)
open TransferPendingFiniteCodec01 (NativePending)
open TransferBoundedNativeCodec01 (ExtendedObject nullifierModulus)
open TransferInstalledSourcePublication01 (SourceRequest installRequests)
open TransferSourceTypedInputProjection01 (typedWords)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBlockPendingSequence01 (allInputs)
open TransferTaggedCodecPublication01 (OtherFinalizationWrites)
open TransferInjectiveKeyPublication01 (keyCode)
open TransferWordSourceDriver01 (runCompleteBlock installSourceOrderedTaggedIo)
/-! Checked getter at the actual published modeled state. Success comes from
the returned whole driver: no desired final object, supported domain, codec
inverse or successful getter is supplied. The old extended unsupported ghost
carrier is explicitly a panic sentinel here, and cannot default. Native
Any/downcast/Clone/layers/imbl/compiler/trace/ownership/OS remain separate.
No native, negative-control or certification credit. -/

def checkedNativeEntry {Other : Type} : Option (ExtendedObject (WordTaggedObject Other)) → Except Unit NativePending
  | none => .ok (.opened [] [])
  | some (.inl object) => TransferWordObjectRead01.sourcePending (some object)
  | some (.inr _) => .error ()

theorem returned_whole_word_driver_derives_successful_checked_getter_and_exact_boundary {Other E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject (WordTaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (WordTaggedObject Other))) (queued : List A)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (WordTaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (WordTaggedObject Other)) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject (WordTaggedObject Other))) (height : Fin (2 ^ 64))
    (outcome : TransferEndToEnd01.Outcome (ExtendedObject (WordTaggedObject Other)) A) (root : Nat)
    (returned : runCompleteBlock inputs wordOf sourceRequests verifiable nonverifiable otherObjects queued writesOf baseIo host height = some outcome)
    (success : outcome.root = some root) :
    ∃ (final : State (ExtendedObject (WordTaggedObject Other)) × List A)
      (state : State (ExtendedObject (WordTaggedObject Other))) (frozen : TransferWriterPrepareSource01.Frozen),
      outcome = TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) {host with active := final.1} height final.2 ∧
      (TransferHostEndBlock01.transferred (installSourceOrderedTaggedIo writesOf baseIo).ending {host with active := final.1} height final.2).returned = some state ∧
      allInputs (installRequests inputs wordOf sourceRequests) =
        (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
      state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) =
        some (.inl (encodeNative (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) ∧
      checkedNativeEntry (state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes)) =
        .ok (.sealed (allInputs (installRequests inputs wordOf sourceRequests))) ∧
      (allInputs (installRequests inputs wordOf sourceRequests)).Nodup ∧
      (allInputs (installRequests inputs wordOf sourceRequests)).length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
      (∀ key ∈ allInputs (installRequests inputs wordOf sourceRequests), key < nullifierModulus) ∧
      frozen.insertions.accepted = allInputs (installRequests inputs wordOf sourceRequests) ∧ frozen.next.applicationRoot = some root ∧
      outcome.host.writer = .ready frozen.next ∧ outcome.host.phase = .idle ∧
      outcome.host.store.actualRoots = frozen.next.nullifiers.roots ∧ outcome.host.store.boundary = some frozen.next.nullifiers := by
  obtain ⟨final, _, reached, values, state, transferred, object, unique, capacity, canonical,
      frozen, accepted, appRoot, ready, idle, roots, boundary⟩ :=
    TransferWordSourceDriver01.returned_whole_block_derives_actual_walk_exact_inputs_and_publication
      inputs wordOf sourceRequests verifiable nonverifiable otherObjects queued writesOf baseIo host height outcome root returned success
  have checked : checkedNativeEntry (state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes)) =
      .ok (.sealed (allInputs (installRequests inputs wordOf sourceRequests))) := by
    rw [object]
    exact TransferWordObjectRead01.canonical_bounded_sealed_object_checked_read_recovers_exact_pending
      (allInputs (installRequests inputs wordOf sourceRequests)) capacity canonical
  exact ⟨final, state, frozen, reached, transferred, values, object, checked, unique, capacity, canonical,
    accepted, appRoot, ready, idle, roots, boundary⟩

set_option pp.all true in
#check @checkedNativeEntry
#print axioms checkedNativeEntry
set_option pp.all true in
#check @returned_whole_word_driver_derives_successful_checked_getter_and_exact_boundary
#print axioms returned_whole_word_driver_derives_successful_checked_getter_and_exact_boundary
end ShielddSecurity.TransferCheckedWordPublication01
