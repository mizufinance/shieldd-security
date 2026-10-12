import ShielddSecurity.TransferNullifierConsensusLimits01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWholeReaderRefusal01
open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01
open TransferVerificationEqualitySource01 (Item)
open TransferReadback (Store Boundary Status MerkleContract)
open TransferNullifierConsensusLimits01 (SupportedWidth)

/-! Source consensus-capacity whole body/refusal join. Config bundles the
already explicit model arguments; delivery instantiates the same full program,
not a caller-supplied execution callback. Each observable refusal derives
failure for both proof contexts/every index mode and preserves original parent
and deferred queue through finish. Failed getter/boundary/lock observations
are unavailable, never unspent. Authenticated spent refusal has the explicit
Merkle soundness contract. Native typed/codec/store/hash/lock/ownership/
boundary/token/Host/durability interfaces remain separate. Formal refusal is
not an executed semantic negative control; panics are outside returned results. -/

structure Config (O E K X Tree A : Type) where
  api : Api O E A
  keys : Keys
  convert : A → Option Encoded
  indexAvailable : Delta O E → Nat → Bool
  raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X)
  notes : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X)
  volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X)
  sct : TransferSctInsertionSource01.Backend O E X Tree
  volumeAvailable : Delta O E → Bool
  decode : O → Store
  readerKey : Nat
  readBoundary : Delta O E → Option Boundary
  lockAvailable : Delta O E → Bool
  hash : String → Nat → List Nat
  verify : Nat → List Nat → Nat → Bool → Bool
  candidate : Delta O E → Nat → Option (Bool × Nat)
  extract : A → TransferCapabilitySource01.ProofContext → Except K Item
  inputs : A → List Nat
  outputs : A → List Nat
  width : Nat
  treeKey : Nat
  notesKey : Nat
  volumeKey : Nat
  payload : Nat
  nullifierKey : Nat
  entryKey : Nat
  dayKey : Nat

def delivery {O E K X Tree A : Type} (config : Config O E K X Tree A)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item) : Api O E A :=
  TransferOrdinaryIndexDelivery01.combinedApi config.api config.keys TransferIndexCountCodec01.codec
    (TransferOrdinaryIndexReadSource01.installReads config.convert config.indexAvailable)
    (TransferDeferredBodyFailure01.executeBound
      (TransferWholeDurableReadback01.installReader config.raw config.decode config.readerKey config.readBoundary
        config.lockAvailable config.hash config.verify config.candidate)
      config.notes config.volume config.sct config.volumeAvailable config.extract config.inputs config.outputs
      (TransferNullifierConsensusLimits01.nativeWordMax config.width) TransferNullifierConsensusLimits01.blockCapacity
      config.treeKey config.notesKey config.volumeKey config.payload config.nullifierKey config.entryKey config.dayKey context action item)

theorem excluded_success_preserves_parent_and_queue {O E A : Type} (parent : State O) (queued : List A)
    (attempted : Option (Commit O E A)) (excluded : ∀ committed, attempted ≠ some committed) :
    attempted = none ∧ finish parent queued attempted = (parent, queued) := by
  cases attempted with
  | none => exact ⟨rfl, rfl⟩
  | some committed => exact False.elim (excluded committed rfl)

theorem whole_success_member_observations {O E K X Tree A : Type} (config : Config O E K X Tree A)
    (supported : SupportedWidth config.width) (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A) (committed : Commit O E A)
    (key : Nat) (inside : key ∈ config.inputs action)
    (success : run (delivery config context action item) registryMatches exclusive mode action parent queued = some committed) :
    ∃ (store : Store) (boundary : Boundary) (response : Status),
      TransferWholeDurableReadback01.currentReader config.decode config.readerKey ⟨parent, (empty : Cache O E)⟩ = some store ∧
      config.readBoundary ⟨parent, (empty : Cache O E)⟩ = some boundary ∧ config.lockAvailable ⟨parent, (empty : Cache O E)⟩ = true ∧
      TransferReadback.status config.hash config.verify store boundary key (config.candidate ⟨parent, (empty : Cache O E)⟩ key) = some response ∧
      response.spent = false := by
  exact TransferNullifierConsensusLimits01.whole_verified_unspent_at_consensus_capacity config.api config.keys config.convert config.indexAvailable
    config.raw config.notes config.volume config.sct config.volumeAvailable config.decode config.readerKey config.readBoundary config.lockAvailable
    config.hash config.verify config.candidate config.extract config.inputs config.outputs config.width supported config.treeKey config.notesKey
    config.volumeKey config.payload config.nullifierKey config.entryKey config.dayKey context action item registryMatches exclusive mode parent queued committed
    (TransferCurrentPendingReplay01.member_derives_nonempty (config.inputs action) key inside) success key inside

theorem whole_missing_reader_preserves_parent_and_queue {O E K X Tree A : Type} (config : Config O E K X Tree A)
    (supported : SupportedWidth config.width) (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A)
    (key : Nat) (inside : key ∈ config.inputs action) (missing : parent.objects config.readerKey = none) :
    let attempted := run (delivery config context action item) registryMatches exclusive mode action parent queued
    attempted = none ∧ finish parent queued attempted = (parent, queued) := by
  dsimp only
  apply excluded_success_preserves_parent_and_queue
  intro committed success
  obtain ⟨_, _, _, reader, _, _, _, _⟩ := whole_success_member_observations config supported context action item
    registryMatches exclusive mode parent queued committed key inside success
  have absent := TransferWholeDurableReadback01.current_reader_absence config.decode config.readerKey ⟨parent, (empty : Cache O E)⟩
    (by simpa only [apply_empty] using missing)
  rw [absent] at reader
  contradiction

theorem whole_missing_boundary_preserves_parent_and_queue {O E K X Tree A : Type} (config : Config O E K X Tree A)
    (supported : SupportedWidth config.width) (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A)
    (key : Nat) (inside : key ∈ config.inputs action) (missing : config.readBoundary ⟨parent, (empty : Cache O E)⟩ = none) :
    let attempted := run (delivery config context action item) registryMatches exclusive mode action parent queued
    attempted = none ∧ finish parent queued attempted = (parent, queued) := by
  dsimp only
  apply excluded_success_preserves_parent_and_queue
  intro committed success
  obtain ⟨_, _, _, _, boundary, _, _, _⟩ := whole_success_member_observations config supported context action item
    registryMatches exclusive mode parent queued committed key inside success
  rw [missing] at boundary
  contradiction

theorem whole_unavailable_lock_preserves_parent_and_queue {O E K X Tree A : Type} (config : Config O E K X Tree A)
    (supported : SupportedWidth config.width) (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A)
    (key : Nat) (inside : key ∈ config.inputs action) (unavailable : config.lockAvailable ⟨parent, (empty : Cache O E)⟩ = false) :
    let attempted := run (delivery config context action item) registryMatches exclusive mode action parent queued
    attempted = none ∧ finish parent queued attempted = (parent, queued) := by
  dsimp only
  apply excluded_success_preserves_parent_and_queue
  intro committed success
  obtain ⟨_, _, _, _, _, locked, _, _⟩ := whole_success_member_observations config supported context action item
    registryMatches exclusive mode parent queued committed key inside success
  rw [unavailable] at locked
  contradiction

theorem whole_stale_boundary_preserves_parent_and_queue {O E K X Tree A : Type} (config : Config O E K X Tree A)
    (supported : SupportedWidth config.width) (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A)
    (key : Nat) (inside : key ∈ config.inputs action) (readerObject : O) (boundary : Boundary)
    (stored : parent.objects config.readerKey = some readerObject)
    (observed : config.readBoundary ⟨parent, (empty : Cache O E)⟩ = some boundary)
    (stale : (config.decode readerObject).boundary ≠ some boundary) :
    let attempted := run (delivery config context action item) registryMatches exclusive mode action parent queued
    attempted = none ∧ finish parent queued attempted = (parent, queued) := by
  dsimp only
  apply excluded_success_preserves_parent_and_queue
  intro committed success
  obtain ⟨store, requested, response, reader, boundaryRead, _, checked, _⟩ := whole_success_member_observations config supported context action item
    registryMatches exclusive mode parent queued committed key inside success
  have readerValue : TransferWholeDurableReadback01.currentReader config.decode config.readerKey ⟨parent, (empty : Cache O E)⟩ =
      some (config.decode readerObject) := by
    simp only [TransferWholeDurableReadback01.currentReader, apply_empty, stored, Option.map_some]
  rw [readerValue] at reader
  have storeSame := Option.some.inj reader
  rw [observed] at boundaryRead
  have boundarySame := Option.some.inj boundaryRead
  have gate := TransferReadback.status_success_gate config.hash config.verify store requested key (config.candidate ⟨parent, empty⟩ key) response checked
  have current : store.boundary = some requested := gate.2.2.2.1
  exact stale (by rw [storeSame, boundarySame]; exact current)

theorem whole_authenticated_spent_preserves_parent_and_queue {O E K X Tree A : Type} (config : Config O E K X Tree A)
    (supported : SupportedWidth config.width) (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A)
    (key : Nat) (inside : key ∈ config.inputs action) (boundary : Boundary)
    (observed : config.readBoundary ⟨parent, (empty : Cache O E)⟩ = some boundary)
    (leaves : Nat → List Nat → Option String) (merkle : MerkleContract config.verify leaves)
    (spent : leaves (boundary.roots.getD (TransferReadback.partition (TransferReadback.key config.hash key)) 0)
      (TransferReadback.key config.hash key) = some TransferReadback.spentValue) :
    let attempted := run (delivery config context action item) registryMatches exclusive mode action parent queued
    attempted = none ∧ finish parent queued attempted = (parent, queued) := by
  dsimp only
  apply excluded_success_preserves_parent_and_queue
  intro committed success
  obtain ⟨store, requested, response, _, boundaryRead, _, checked, unspent⟩ := whole_success_member_observations config supported context action item
    registryMatches exclusive mode parent queued committed key inside success
  rw [observed] at boundaryRead
  have boundarySame := Option.some.inj boundaryRead
  have verified := (TransferReadback.status_success_checks config.hash config.verify store requested key (config.candidate ⟨parent, empty⟩ key) response checked).2.2
  rw [unspent] at verified
  have absent := merkle _ _ _ _ verified
  have emptyLeaf : leaves (requested.roots.getD (TransferReadback.partition (TransferReadback.key config.hash key)) 0)
      (TransferReadback.key config.hash key) = none := by
    simpa only [Bool.false_eq_true, if_false] using absent
  rw [← boundarySame, spent] at emptyLeaf
  contradiction

set_option pp.all true in
#check @Config
#print axioms Config
set_option pp.all true in
#check @delivery
#print axioms delivery
set_option pp.all true in
#check @excluded_success_preserves_parent_and_queue
#print axioms excluded_success_preserves_parent_and_queue
set_option pp.all true in
#check @whole_success_member_observations
#print axioms whole_success_member_observations
set_option pp.all true in
#check @whole_missing_reader_preserves_parent_and_queue
#print axioms whole_missing_reader_preserves_parent_and_queue
set_option pp.all true in
#check @whole_missing_boundary_preserves_parent_and_queue
#print axioms whole_missing_boundary_preserves_parent_and_queue
set_option pp.all true in
#check @whole_unavailable_lock_preserves_parent_and_queue
#print axioms whole_unavailable_lock_preserves_parent_and_queue
set_option pp.all true in
#check @whole_stale_boundary_preserves_parent_and_queue
#print axioms whole_stale_boundary_preserves_parent_and_queue
set_option pp.all true in
#check @whole_authenticated_spent_preserves_parent_and_queue
#print axioms whole_authenticated_spent_preserves_parent_and_queue
end ShielddSecurity.TransferWholeReaderRefusal01
