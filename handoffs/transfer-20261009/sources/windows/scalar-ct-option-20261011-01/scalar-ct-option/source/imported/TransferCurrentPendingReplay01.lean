import ShielddSecurity.TransferNullifierObjectKeys01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferCurrentPendingReplay01
open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01
open TransferVerificationEqualitySource01 (Item)
open TransferNullifierBatchSource01 (Pending)

/-! Install the current object-overlay pending read and derive shared-input
replay refusal after a first whole successful delivery. The decoder denotes
the successfully typed object_get/Clone branch, with encode/decode roundtrip
explicit. Rust wrong-type downcast/put and loader panics are outside this
returned-result model, not recoverable errors or defaults. Getter absence
defaults to Open empty. No desired pending-membership/poststate or failing
callback is supplied to the two-action theorem. Native/store/codec/ownership/
reader/key/crypto/token/Host/durability correspondence remains separate. -/

def emptyPending : Pending := ⟨[], fun _ => false, false⟩

def currentPending {O E : Type} (decode : O → Pending) (objectKey : Nat) (child : Delta O E) : Pending :=
  match (applyCache child.parent child.cache).objects objectKey with
  | none => emptyPending
  | some object => decode object

def withPending {O E X : Type} (raw : TransferRawEffectsSource01.Backend O E X)
    (decode : O → Pending) (objectKey : Nat) : TransferRawEffectsSource01.Backend O E X :=
  {raw with nullifiers := {raw.nullifiers with pending := currentPending decode objectKey}}

theorem member_derives_nonempty (inputs : List Nat) (key : Nat) (inside : key ∈ inputs) : inputs.isEmpty = false := by
  cases inputs with
  | nil => cases inside
  | cons head rest => rfl

theorem current_object_absence_derives_default {O E : Type} (decode : O → Pending) (objectKey : Nat) (child : Delta O E)
    (absent : (applyCache child.parent child.cache).objects objectKey = none) :
    currentPending decode objectKey child = emptyPending := by
  simp only [currentPending, absent]

theorem encoded_current_object_derives_pending {O E : Type} (encode : Pending → O) (decode : O → Pending)
    (roundtrip : ∀ pending, decode (encode pending) = pending) (objectKey : Nat) (child : Delta O E) (pending : Pending)
    (stored : (applyCache child.parent child.cache).objects objectKey = some (encode pending)) :
    currentPending decode objectKey child = pending := by
  simp only [currentPending, stored, roundtrip]

theorem stored_current_member_rejects_whole_delivery {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (decode : O → Pending) (roundtrip : ∀ pending, decode (raw.nullifiers.encode pending) = pending)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A)
    (pending : Pending) (shared : Nat) (inside : shared ∈ inputs action) (belowWord : capacity < wordMax)
    (stored : parent.objects nullifierKey = some (raw.nullifiers.encode pending)) (spent : pending.membership shared = true) :
    run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound (withPending raw decode nullifierKey) notes volume sct volumeAvailable extract inputs outputs
        wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item))
      registryMatches exclusive mode action parent queued = none := by
  have current : (withPending raw decode nullifierKey).nullifiers.pending ⟨parent, (empty : Cache O E)⟩ = pending := by
    exact encoded_current_object_derives_pending raw.nullifiers.encode decode roundtrip nullifierKey ⟨parent, empty⟩ pending
      (by simpa only [apply_empty] using stored)
  cases result : run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound (withPending raw decode nullifierKey) notes volume sct volumeAvailable extract inputs outputs
        wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item))
      registryMatches exclusive mode action parent queued with
  | none => rfl
  | some committed =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, fresh⟩ :=
      TransferWholeNullifierAdmission01.whole_delivery_success_derives_every_input_fresh_and_bounded api keys convert indexAvailable
        (withPending raw decode nullifierKey) notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey
        volumeKey payload nullifierKey entryKey dayKey context action item registryMatches exclusive mode parent queued committed
        (member_derives_nonempty (inputs action) shared inside) belowWord result
    have unspent := (fresh shared inside).2.1
    rw [current, spent] at unspent
    contradiction

theorem first_whole_success_then_shared_input_replay_preserves_first_parent_and_queue {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (decode : O → Pending) (roundtrip : ∀ pending, decode (raw.nullifiers.encode pending) = pending)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (wordMax capacity firstPayload firstEntry firstDay secondPayload secondEntry secondDay : Nat)
    (firstContext secondContext : TransferCapabilitySource01.ProofContext) (firstAction secondAction : A) (firstItem secondItem : Item)
    (firstRegistry firstExclusive secondRegistry secondExclusive : Bool) (firstMode secondMode : IndexMode)
    (parent : State O) (queued : List A) (firstCommit : Commit O E A) (shared : Nat)
    (firstMember : shared ∈ inputs firstAction) (secondMember : shared ∈ inputs secondAction) (belowWord : capacity < wordMax)
    (firstSuccess : run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound (withPending raw decode (project TransferNullifierObjectKeys01.nullifierBytes))
        notes volume sct volumeAvailable extract inputs outputs wordMax capacity (project TransferNullifierObjectKeys01.treeBytes)
        (project TransferNullifierObjectKeys01.notesBytes) (project TransferNullifierObjectKeys01.volumeBytes) firstPayload
        (project TransferNullifierObjectKeys01.nullifierBytes) firstEntry firstDay firstContext firstAction firstItem))
      firstRegistry firstExclusive firstMode firstAction parent queued = some firstCommit) :
    let attempted := run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound (withPending raw decode (project TransferNullifierObjectKeys01.nullifierBytes))
        notes volume sct volumeAvailable extract inputs outputs wordMax capacity (project TransferNullifierObjectKeys01.treeBytes)
        (project TransferNullifierObjectKeys01.notesBytes) (project TransferNullifierObjectKeys01.volumeBytes) secondPayload
        (project TransferNullifierObjectKeys01.nullifierBytes) secondEntry secondDay secondContext secondAction secondItem))
      secondRegistry secondExclusive secondMode secondAction firstCommit.parent firstCommit.deferred
    attempted = none ∧ finish firstCommit.parent firstCommit.deferred attempted = (firstCommit.parent, firstCommit.deferred) := by
  dsimp only
  obtain ⟨pending, _, retained, _, _, _, fresh⟩ := TransferNullifierObjectKeys01.whole_success_retains_source_key_pending_nullifier_encoding
    api keys convert indexAvailable (withPending raw decode (project TransferNullifierObjectKeys01.nullifierBytes)) notes volume sct volumeAvailable
    extract inputs outputs project injection wordMax capacity firstPayload firstEntry firstDay firstContext firstAction firstItem
    firstRegistry firstExclusive firstMode parent queued firstCommit (member_derives_nonempty (inputs firstAction) shared firstMember)
    belowWord firstSuccess
  have spent : pending.membership shared = true := (fresh shared firstMember).2.2
  have rejected := stored_current_member_rejects_whole_delivery api keys convert indexAvailable raw notes volume sct volumeAvailable decode roundtrip
    extract inputs outputs wordMax capacity (project TransferNullifierObjectKeys01.treeBytes) (project TransferNullifierObjectKeys01.notesBytes)
    (project TransferNullifierObjectKeys01.volumeBytes) secondPayload (project TransferNullifierObjectKeys01.nullifierBytes) secondEntry secondDay
    secondContext secondAction secondItem secondRegistry secondExclusive secondMode firstCommit.parent firstCommit.deferred pending shared
    secondMember belowWord retained spent
  exact ⟨rejected, by rw [rejected]; rfl⟩

set_option pp.all true in
#check @emptyPending
#print axioms emptyPending
set_option pp.all true in
#check @currentPending
#print axioms currentPending
set_option pp.all true in
#check @withPending
#print axioms withPending
set_option pp.all true in
#check @member_derives_nonempty
#print axioms member_derives_nonempty
set_option pp.all true in
#check @current_object_absence_derives_default
#print axioms current_object_absence_derives_default
set_option pp.all true in
#check @encoded_current_object_derives_pending
#print axioms encoded_current_object_derives_pending
set_option pp.all true in
#check @stored_current_member_rejects_whole_delivery
#print axioms stored_current_member_rejects_whole_delivery
set_option pp.all true in
#check @first_whole_success_then_shared_input_replay_preserves_first_parent_and_queue
#print axioms first_whole_success_then_shared_input_replay_preserves_first_parent_and_queue
end ShielddSecurity.TransferCurrentPendingReplay01
