import ShielddSecurity.TransferBlockPendingSequence01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferPendingSealSource01
open TransferStateDelta TransferRawStateProgram01
open TransferNullifierBatchSource01 (Pending)

/-! Pinned SCT one-shot seal, pending ordered read and ensure-sealed branches.
Absence defaults to empty Open for seal, but ensure-sealed accepts absence.
Sealing writes one typed object, freezes exact order and derives membership
from that order, preserving all V/NV/event cache domains and other objects.
Already Sealed is an error retaining the input cache. No NOMT or persistent
storage operation is modeled here. Typed enum/Clone/getter/encode/decode/native
collection/ownership correspondence remains explicit; wrong-type object
panics are outside returned results. No native/semantic-control/full claim
certification credit. -/

inductive SealError where
  | alreadySealed | notSealed

def freeze (pending : Pending) : Pending :=
  ⟨pending.ordered, fun key => pending.ordered.contains key, true⟩

def seal {O E : Type} (encode : Pending → O) (decode : O → Pending) (objectKey : Nat) (child : Delta O E) : Outcome O E SealError :=
  let pending := TransferCurrentPendingReplay01.currentPending decode objectKey child
  if pending.sealed then ⟨child.cache, .error .alreadySealed⟩
  else ⟨(putObject child objectKey (some (encode (freeze pending)))).cache, .ok ()⟩

def ensureSealed {O E : Type} (decode : O → Pending) (objectKey : Nat) (child : Delta O E) : Except SealError Unit :=
  match (applyCache child.parent child.cache).objects objectKey with
  | none => .ok ()
  | some object => if (decode object).sealed then .ok () else .error .notSealed

theorem freeze_exact_order_membership_and_sealed (pending : Pending) :
    (freeze pending).ordered = pending.ordered ∧ TransferPendingSetInvariant01.Coherent (freeze pending) ∧
      (freeze pending).sealed = true := by
  exact ⟨rfl, fun _ => rfl, rfl⟩

theorem absent_ensure_succeeds {O E : Type} (decode : O → Pending) (objectKey : Nat) (child : Delta O E)
    (absent : (applyCache child.parent child.cache).objects objectKey = none) :
    ensureSealed decode objectKey child = .ok () := by
  simp only [ensureSealed, absent]

theorem encoded_open_ensure_refuses {O E : Type} (encode : Pending → O) (decode : O → Pending)
    (roundtrip : ∀ pending, decode (encode pending) = pending) (objectKey : Nat) (child : Delta O E) (pending : Pending)
    (stored : (applyCache child.parent child.cache).objects objectKey = some (encode pending)) (opened : pending.sealed = false) :
    ensureSealed decode objectKey child = .error .notSealed := by
  simp only [ensureSealed, stored, roundtrip, opened, Bool.false_eq_true, if_false]

theorem encoded_frozen_ensure_succeeds {O E : Type} (encode : Pending → O) (decode : O → Pending)
    (roundtrip : ∀ pending, decode (encode pending) = pending) (objectKey : Nat) (child : Delta O E) (pending : Pending)
    (stored : (applyCache child.parent child.cache).objects objectKey = some (encode (freeze pending))) :
    ensureSealed decode objectKey child = .ok () := by
  simp only [ensureSealed, stored, roundtrip, freeze, if_true]

theorem opened_seal_derives_single_object_and_frames {O E : Type} (encode : Pending → O) (decode : O → Pending)
    (objectKey : Nat) (child : Delta O E)
    (opened : (TransferCurrentPendingReplay01.currentPending decode objectKey child).sealed = false) :
    (seal encode decode objectKey child).result = .ok () ∧
      (seal encode decode objectKey child).cache.verifiable = child.cache.verifiable ∧
      (seal encode decode objectKey child).cache.nonverifiable = child.cache.nonverifiable ∧
      (seal encode decode objectKey child).cache.events = child.cache.events ∧
      (∀ other, other ≠ objectKey → (seal encode decode objectKey child).cache.objects other = child.cache.objects other) ∧
      (applyCache child.parent (seal encode decode objectKey child).cache).objects objectKey =
        some (encode (freeze (TransferCurrentPendingReplay01.currentPending decode objectKey child))) := by
  simp only [seal, opened, Bool.false_eq_true, if_false]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro other different
    simp only [putObject, if_neg different]
  · exact object_write_visible_in_child child objectKey _

theorem already_sealed_error_retains_input_cache {O E : Type} (encode : Pending → O) (decode : O → Pending)
    (objectKey : Nat) (child : Delta O E)
    (sealed : (TransferCurrentPendingReplay01.currentPending decode objectKey child).sealed = true) :
    seal encode decode objectKey child = ⟨child.cache, .error .alreadySealed⟩ := by
  simp only [seal, sealed, if_true]

theorem absence_seals_default_empty_order {O E : Type} (encode : Pending → O) (decode : O → Pending)
    (objectKey : Nat) (child : Delta O E) (absent : (applyCache child.parent child.cache).objects objectKey = none) :
    seal encode decode objectKey child =
      ⟨(putObject child objectKey (some (encode (freeze TransferCurrentPendingReplay01.emptyPending)))).cache, .ok ()⟩ := by
  have default := TransferCurrentPendingReplay01.current_object_absence_derives_default decode objectKey child absent
  simp only [seal, default, TransferCurrentPendingReplay01.emptyPending, Bool.false_eq_true, if_false]

theorem successful_seal_current_read_freezes_and_repeat_refuses {O E : Type} (encode : Pending → O) (decode : O → Pending)
    (roundtrip : ∀ pending, decode (encode pending) = pending) (objectKey : Nat) (child : Delta O E)
    (opened : (TransferCurrentPendingReplay01.currentPending decode objectKey child).sealed = false) :
    let output := seal encode decode objectKey child
    let after : Delta O E := ⟨child.parent, output.cache⟩
    TransferCurrentPendingReplay01.currentPending decode objectKey after =
      freeze (TransferCurrentPendingReplay01.currentPending decode objectKey child) ∧
      ensureSealed decode objectKey after = .ok () ∧
      seal encode decode objectKey after = ⟨output.cache, .error .alreadySealed⟩ := by
  dsimp only
  have stored := (opened_seal_derives_single_object_and_frames encode decode objectKey child opened).2.2.2.2.2
  have frozenRead := TransferCurrentPendingReplay01.encoded_current_object_derives_pending encode decode roundtrip objectKey
    ⟨child.parent, (seal encode decode objectKey child).cache⟩ (freeze (TransferCurrentPendingReplay01.currentPending decode objectKey child)) stored
  refine ⟨frozenRead, encoded_frozen_ensure_succeeds encode decode roundtrip objectKey _ _ stored, ?_⟩
  apply already_sealed_error_retains_input_cache
  rw [frozenRead]
  rfl

theorem whole_request_after_current_sealing_preserves_parent_and_queue {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (project : Bytes → Nat) (injection : Function.Injective project)
    (request : TransferBlockPendingSequence01.Request O E K X Tree A) (parent : State O) (queued : List A)
    (sealed : (TransferBlockPendingSequence01.parentPending decode project parent).sealed = true) :
    let attempted := TransferBlockPendingSequence01.step encode decode project request parent queued
    attempted = none ∧ finish parent queued attempted = (parent, queued) := by
  dsimp only
  apply TransferWholeReaderRefusal01.excluded_success_preserves_parent_and_queue
  intro committed success
  let config := request.config
  let raw := TransferWholeDurableReadback01.installReader
    (TransferBlockPendingSequence01.bindPending config encode decode project).raw config.decode config.readerKey config.readBoundary
    config.lockAvailable config.hash config.verify config.candidate
  obtain ⟨pending, inspected, _, _, _, _, _⟩ :=
    TransferNullifierObjectKeys01.whole_success_retains_source_key_pending_nullifier_encoding config.api config.keys config.convert config.indexAvailable
      raw config.notes config.volume config.sct config.volumeAvailable config.extract config.inputs config.outputs project injection
      (TransferNullifierConsensusLimits01.nativeWordMax config.width) TransferNullifierConsensusLimits01.blockCapacity config.payload config.entryKey config.dayKey
      request.context request.action request.item request.registryMatches request.exclusive request.mode parent queued committed request.nonempty
      (TransferNullifierConsensusLimits01.capacity_below_supported_word config.width request.supported) success
  obtain ⟨previous, _, previousEq, _, opened, _, _, _, _, _⟩ :=
    TransferNullifierBatchSource01.inspection_success_order raw.nullifiers (TransferNullifierConsensusLimits01.nativeWordMax config.width)
      TransferNullifierConsensusLimits01.blockCapacity ⟨parent, (empty : Cache O E)⟩ (config.inputs request.action) pending inspected
  subst previous
  have openParent : (TransferBlockPendingSequence01.parentPending decode project parent).sealed = false := by
    change (TransferCurrentPendingReplay01.currentPending decode (project TransferNullifierObjectKeys01.nullifierBytes)
      ⟨parent, (empty : Cache O E)⟩).sealed = false at opened
    simpa only [TransferBlockPendingSequence01.parentPending, TransferCurrentPendingReplay01.currentPending, apply_empty] using opened
  rw [sealed] at openParent
  contradiction

set_option pp.all true in
#check @SealError
#print axioms SealError
set_option pp.all true in
#check @freeze
#print axioms freeze
set_option pp.all true in
#check @seal
#print axioms seal
set_option pp.all true in
#check @ensureSealed
#print axioms ensureSealed
set_option pp.all true in
#check @freeze_exact_order_membership_and_sealed
#print axioms freeze_exact_order_membership_and_sealed
set_option pp.all true in
#check @absent_ensure_succeeds
#print axioms absent_ensure_succeeds
set_option pp.all true in
#check @encoded_open_ensure_refuses
#print axioms encoded_open_ensure_refuses
set_option pp.all true in
#check @encoded_frozen_ensure_succeeds
#print axioms encoded_frozen_ensure_succeeds
set_option pp.all true in
#check @opened_seal_derives_single_object_and_frames
#print axioms opened_seal_derives_single_object_and_frames
set_option pp.all true in
#check @already_sealed_error_retains_input_cache
#print axioms already_sealed_error_retains_input_cache
set_option pp.all true in
#check @absence_seals_default_empty_order
#print axioms absence_seals_default_empty_order
set_option pp.all true in
#check @successful_seal_current_read_freezes_and_repeat_refuses
#print axioms successful_seal_current_read_freezes_and_repeat_refuses
set_option pp.all true in
#check @whole_request_after_current_sealing_preserves_parent_and_queue
#print axioms whole_request_after_current_sealing_preserves_parent_and_queue
end ShielddSecurity.TransferPendingSealSource01
