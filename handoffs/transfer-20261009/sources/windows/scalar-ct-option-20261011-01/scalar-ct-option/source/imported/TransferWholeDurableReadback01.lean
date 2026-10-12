import ShielddSecurity.TransferCurrentPendingReplay01
import ShielddSecurity.TransferReadback
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferWholeDurableReadback01
open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01
open TransferVerificationEqualitySource01 (Item)
open TransferReadback (Store Boundary Status ReadGate MerkleContract)

/-! Current typed Reader object, observed authenticated application boundary,
read-lock availability and verified status are installed in the full body.
Successful whole delivery derives a verified unspent status for every input.
Merkle semantic absence is conditional on the existing explicit soundness
contract. Boundary decoding/authentication, typed object_get/Clone/locks,
native NOMT/hash/codec correspondence and durability remain interfaces.
Wrong-type object panics are outside this successfully typed result model.
No ready/store/boundary/lookup/proof success is supplied to whole-success
theorems. Reader absence and operational errors never denote unspent. -/

def currentReader {O E : Type} (decode : O → Store) (readerKey : Nat) (child : Delta O E) : Option Store :=
  ((applyCache child.parent child.cache).objects readerKey).map decode

def lookup {O E : Type} (decode : O → Store) (readerKey : Nat)
    (readBoundary : Delta O E → Option Boundary) (lockAvailable : Delta O E → Bool)
    (hash : String → Nat → List Nat) (verify : Nat → List Nat → Nat → Bool → Bool)
    (candidate : Delta O E → Nat → Option (Bool × Nat)) (child : Delta O E) (key : Nat) : Option Bool :=
  match currentReader decode readerKey child with
  | none => none
  | some store =>
    match readBoundary child with
    | none => none
    | some boundary =>
      if lockAvailable child then
        (TransferReadback.status hash verify store boundary key (candidate child key)).map (fun status => status.spent)
      else none

def installReader {O E X : Type} (raw : TransferRawEffectsSource01.Backend O E X)
    (decode : O → Store) (readerKey : Nat) (readBoundary : Delta O E → Option Boundary)
    (lockAvailable : Delta O E → Bool) (hash : String → Nat → List Nat)
    (verify : Nat → List Nat → Nat → Bool → Bool) (candidate : Delta O E → Nat → Option (Bool × Nat)) :
    TransferRawEffectsSource01.Backend O E X :=
  {raw with nullifiers := {raw.nullifiers with
    readerGate := fun child => (currentReader decode readerKey child).isSome
    lookup := lookup decode readerKey readBoundary lockAvailable hash verify candidate}}

theorem current_reader_absence {O E : Type} (decode : O → Store) (readerKey : Nat) (child : Delta O E)
    (absent : (applyCache child.parent child.cache).objects readerKey = none) :
    currentReader decode readerKey child = none := by
  simp only [currentReader, absent, Option.map_none]

theorem lookup_missing_reader_unavailable {O E : Type} (decode : O → Store) (readerKey : Nat)
    (readBoundary : Delta O E → Option Boundary) (lockAvailable : Delta O E → Bool)
    (hash : String → Nat → List Nat) (verify : Nat → List Nat → Nat → Bool → Bool)
    (candidate : Delta O E → Nat → Option (Bool × Nat)) (child : Delta O E) (key : Nat)
    (missing : currentReader decode readerKey child = none) :
    lookup decode readerKey readBoundary lockAvailable hash verify candidate child key = none := by
  simp only [lookup, missing]

theorem lookup_missing_boundary_unavailable {O E : Type} (decode : O → Store) (readerKey : Nat)
    (readBoundary : Delta O E → Option Boundary) (lockAvailable : Delta O E → Bool)
    (hash : String → Nat → List Nat) (verify : Nat → List Nat → Nat → Bool → Bool)
    (candidate : Delta O E → Nat → Option (Bool × Nat)) (child : Delta O E) (key : Nat)
    (missing : readBoundary child = none) :
    lookup decode readerKey readBoundary lockAvailable hash verify candidate child key = none := by
  cases observed : currentReader decode readerKey child <;> simp only [lookup, observed, missing]

theorem lookup_unavailable_lock {O E : Type} (decode : O → Store) (readerKey : Nat)
    (readBoundary : Delta O E → Option Boundary) (lockAvailable : Delta O E → Bool)
    (hash : String → Nat → List Nat) (verify : Nat → List Nat → Nat → Bool → Bool)
    (candidate : Delta O E → Nat → Option (Bool × Nat)) (child : Delta O E) (key : Nat)
    (unavailable : lockAvailable child = false) :
    lookup decode readerKey readBoundary lockAvailable hash verify candidate child key = none := by
  cases reader : currentReader decode readerKey child with
  | none => simp only [lookup, reader]
  | some store => cases boundary : readBoundary child <;> simp only [lookup, reader, boundary, unavailable, Bool.false_eq_true, if_false]

theorem lookup_stale_boundary_unavailable {O E : Type} (decode : O → Store) (readerKey : Nat)
    (readBoundary : Delta O E → Option Boundary) (lockAvailable : Delta O E → Bool)
    (hash : String → Nat → List Nat) (verify : Nat → List Nat → Nat → Bool → Bool)
    (candidate : Delta O E → Nat → Option (Bool × Nat)) (child : Delta O E) (key : Nat) (store : Store) (boundary : Boundary)
    (reader : currentReader decode readerKey child = some store) (observed : readBoundary child = some boundary)
    (stale : store.boundary ≠ some boundary) :
    lookup decode readerKey readBoundary lockAvailable hash verify candidate child key = none := by
  cases locked : lockAvailable child with
  | false => simp only [lookup, reader, observed, locked, Bool.false_eq_true, if_false]
  | true =>
    simp only [lookup, reader, observed, locked, if_true,
      TransferReadback.stale_boundary_unavailable hash verify store boundary key (candidate child key) stale, Option.map_none]

theorem lookup_success_observes_verified_status {O E : Type} (decode : O → Store) (readerKey : Nat)
    (readBoundary : Delta O E → Option Boundary) (lockAvailable : Delta O E → Bool)
    (hash : String → Nat → List Nat) (verify : Nat → List Nat → Nat → Bool → Bool)
    (candidate : Delta O E → Nat → Option (Bool × Nat)) (child : Delta O E) (key : Nat)
    (success : lookup decode readerKey readBoundary lockAvailable hash verify candidate child key = some false) :
    ∃ (store : Store) (boundary : Boundary) (response : Status),
      currentReader decode readerKey child = some store ∧ readBoundary child = some boundary ∧
      lockAvailable child = true ∧ TransferReadback.status hash verify store boundary key (candidate child key) = some response ∧
      response.spent = false := by
  cases reader : currentReader decode readerKey child with
  | none => simp only [lookup, reader] at success; contradiction
  | some store =>
    cases boundaryRead : readBoundary child with
    | none => simp only [lookup, reader, boundaryRead] at success; contradiction
    | some boundary =>
      cases locked : lockAvailable child with
      | false => simp only [lookup, reader, boundaryRead, locked, Bool.false_eq_true, if_false] at success; contradiction
      | true =>
        cases checked : TransferReadback.status hash verify store boundary key (candidate child key) with
        | none => simp only [lookup, reader, boundaryRead, locked, if_true, checked, Option.map_none] at success; contradiction
        | some response =>
          have unspent : response.spent = false := Option.some.inj
            (by simpa only [lookup, reader, boundaryRead, locked, if_true, checked, Option.map_some] using success)
          exact ⟨store, boundary, response, rfl, rfl, rfl, checked, unspent⟩

theorem whole_success_every_input_verified_unspent {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (decode : O → Store) (readerKey : Nat) (readBoundary : Delta O E → Option Boundary)
    (lockAvailable : Delta O E → Bool) (hash : String → Nat → List Nat)
    (verify : Nat → List Nat → Nat → Bool → Bool) (candidate : Delta O E → Nat → Option (Bool × Nat))
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A) (committed : Commit O E A)
    (nonempty : (inputs action).isEmpty = false) (belowWord : capacity < wordMax)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound (installReader raw decode readerKey readBoundary lockAvailable hash verify candidate)
        notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item))
      registryMatches exclusive mode action parent queued = some committed) :
    ∀ key ∈ inputs action, ∃ (store : Store) (boundary : Boundary) (response : Status),
      currentReader decode readerKey ⟨parent, (empty : Cache O E)⟩ = some store ∧
      readBoundary ⟨parent, (empty : Cache O E)⟩ = some boundary ∧ lockAvailable ⟨parent, (empty : Cache O E)⟩ = true ∧
      TransferReadback.status hash verify store boundary key (candidate ⟨parent, (empty : Cache O E)⟩ key) = some response ∧ response.spent = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, fresh⟩ :=
    TransferWholeNullifierAdmission01.whole_delivery_success_derives_every_input_fresh_and_bounded api keys convert indexAvailable
      (installReader raw decode readerKey readBoundary lockAvailable hash verify candidate) notes volume sct volumeAvailable extract inputs outputs
      wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item registryMatches exclusive mode parent queued committed
      nonempty belowWord success
  intro key inside
  exact lookup_success_observes_verified_status decode readerKey readBoundary lockAvailable hash verify candidate ⟨parent, empty⟩ key (fresh key inside).1

theorem whole_success_every_input_authenticated_absence {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (decode : O → Store) (readerKey : Nat) (readBoundary : Delta O E → Option Boundary)
    (lockAvailable : Delta O E → Bool) (hash : String → Nat → List Nat)
    (verify : Nat → List Nat → Nat → Bool → Bool) (candidate : Delta O E → Nat → Option (Bool × Nat))
    (leaves : Nat → List Nat → Option String) (merkle : MerkleContract verify leaves)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A) (committed : Commit O E A)
    (nonempty : (inputs action).isEmpty = false) (belowWord : capacity < wordMax)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound (installReader raw decode readerKey readBoundary lockAvailable hash verify candidate)
        notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item))
      registryMatches exclusive mode action parent queued = some committed) :
    ∀ key ∈ inputs action, ∃ (store : Store) (boundary : Boundary) (response : Status),
      currentReader decode readerKey ⟨parent, (empty : Cache O E)⟩ = some store ∧
      readBoundary ⟨parent, (empty : Cache O E)⟩ = some boundary ∧ lockAvailable ⟨parent, (empty : Cache O E)⟩ = true ∧
      ReadGate store boundary (TransferReadback.key hash key) ∧ TransferReadback.partition (TransferReadback.key hash key) < 16 ∧
      response.nullifier = key ∧ response.boundary = boundary ∧ response.spent = false ∧
      verify (boundary.roots.getD (TransferReadback.partition (TransferReadback.key hash key)) 0)
        (TransferReadback.key hash key) response.proof false = true ∧
      leaves (boundary.roots.getD (TransferReadback.partition (TransferReadback.key hash key)) 0) (TransferReadback.key hash key) = none := by
  intro key inside
  obtain ⟨store, boundary, response, reader, boundaryRead, locked, checked, unspent⟩ :=
    whole_success_every_input_verified_unspent api keys convert indexAvailable raw notes volume sct volumeAvailable decode readerKey readBoundary lockAvailable
      hash verify candidate extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item
      registryMatches exclusive mode parent queued committed nonempty belowWord success key inside
  have gate := TransferReadback.status_success_gate hash verify store boundary key (candidate ⟨parent, empty⟩ key) response checked
  have partitioned := TransferReadback.status_partition_bounded hash verify store boundary key (candidate ⟨parent, empty⟩ key) response checked
  have checks := TransferReadback.status_success_checks hash verify store boundary key (candidate ⟨parent, empty⟩ key) response checked
  have verified := checks.2.2
  rw [unspent] at verified
  have absent := merkle _ _ _ _ verified
  exact ⟨store, boundary, response, reader, boundaryRead, locked, gate, partitioned, checks.1, checks.2.1, unspent, verified,
    by simpa only [Bool.false_eq_true, if_false] using absent⟩

set_option pp.all true in
#check @currentReader
#print axioms currentReader
set_option pp.all true in
#check @lookup
#print axioms lookup
set_option pp.all true in
#check @installReader
#print axioms installReader
set_option pp.all true in
#check @current_reader_absence
#print axioms current_reader_absence
set_option pp.all true in
#check @lookup_missing_reader_unavailable
#print axioms lookup_missing_reader_unavailable
set_option pp.all true in
#check @lookup_missing_boundary_unavailable
#print axioms lookup_missing_boundary_unavailable
set_option pp.all true in
#check @lookup_unavailable_lock
#print axioms lookup_unavailable_lock
set_option pp.all true in
#check @lookup_stale_boundary_unavailable
#print axioms lookup_stale_boundary_unavailable
set_option pp.all true in
#check @lookup_success_observes_verified_status
#print axioms lookup_success_observes_verified_status
set_option pp.all true in
#check @whole_success_every_input_verified_unspent
#print axioms whole_success_every_input_verified_unspent
set_option pp.all true in
#check @whole_success_every_input_authenticated_absence
#print axioms whole_success_every_input_authenticated_absence
end ShielddSecurity.TransferWholeDurableReadback01
