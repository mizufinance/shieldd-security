import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferReadback

/-!
Independent result model for owned permanent-nullifier Reader/Store/Query and
SCT pending membership. None represents unavailable/error, never unspent.
Root and proof identities are abstract; byte codecs, SHA256, locking, NOMT,
recovery history and actual Rust correspondence remain explicit contracts.
A retained published boundary does not imply the shared store can serve it.
-/

def keyDomain : String := "shieldd.spend-nullifier.v1" ++ String.singleton (Char.ofNat 0)
def rootsDomain : String := "shieldd.nomt.roots.v1" ++ String.singleton (Char.ofNat 0)
def spentValue : String := "shieldd.spent.v1"

structure Boundary where
  height : Option Nat
  blockId : List Nat
  roots : List Nat
  deriving DecidableEq

structure Store where
  ready : Bool
  healthy : Bool
  actualRoots : List Nat
  boundary : Option Boundary

structure Status where
  nullifier : Nat
  boundary : Boundary
  spent : Bool
  proof : Nat

def key (hash : String → Nat → List Nat) (nullifier : Nat) : List Nat :=
  hash keyDomain nullifier

def partition (path : List Nat) : Nat := path.getD 0 0 / 16

/-- 16 is encoded as the two big-endian bytes [0,16], before ordered roots.
The abstract root encoding must be instantiated with 32 bytes per native root. -/
def rootsCommitment (hash : String → List Nat → List Nat → Nat) (roots : List Nat) : Nat :=
  hash rootsDomain [0, 16] roots

def ReadGate (store : Store) (requested : Boundary) (path : List Nat) : Prop :=
  store.ready = true ∧ store.healthy = true ∧
  store.actualRoots = requested.roots ∧ store.boundary = some requested ∧
  requested.roots.length = 16 ∧ path.length = 32 ∧ path.getD 0 0 < 256

instance (store : Store) (requested : Boundary) (path : List Nat) :
    Decidable (ReadGate store requested path) := by
  unfold ReadGate
  infer_instance

def status (hash : String → Nat → List Nat)
    (verify : Nat → List Nat → Nat → Bool → Bool)
    (store : Store) (requested : Boundary) (nullifier : Nat)
    (candidate : Option (Bool × Nat)) : Option Status :=
  let path := key hash nullifier
  if ReadGate store requested path then
    match candidate with
    | none => none
    | some (spent, proof) =>
        if verify (requested.roots.getD (partition path) 0) path proof spent = true then
          some ⟨nullifier, requested, spent, proof⟩
        else none
  else none

theorem status_success_gate (hash verify store requested nullifier candidate response)
    (success : status hash verify store requested nullifier candidate = some response) :
    ReadGate store requested (key hash nullifier) := by
  by_cases gate : ReadGate store requested (key hash nullifier)
  · exact gate
  · simp [status, gate] at success

theorem status_success_checks (hash verify store requested nullifier candidate response)
    (success : status hash verify store requested nullifier candidate = some response) :
    response.nullifier = nullifier ∧ response.boundary = requested ∧
    verify (requested.roots.getD (partition (key hash nullifier)) 0)
      (key hash nullifier) response.proof response.spent = true := by
  have gate := status_success_gate hash verify store requested nullifier candidate response success
  cases candidate with
  | none => simp [status, gate] at success
  | some candidate =>
      rcases candidate with ⟨spent, proof⟩
      by_cases valid : verify (requested.roots.getD (partition (key hash nullifier)) 0)
          (key hash nullifier) proof spent = true
      · have same : (Status.mk nullifier requested spent proof) = response :=
          Option.some.inj (by simpa only [status, if_pos gate, if_pos valid] using success)
        rw [← same]
        exact ⟨rfl, rfl, valid⟩
      · have impossible : (none : Option Status) = some response := by
          simpa only [status, if_pos gate, if_neg valid] using success
        cases impossible

theorem status_partition_bounded (hash verify store requested nullifier candidate response)
    (success : status hash verify store requested nullifier candidate = some response) :
    partition (key hash nullifier) < 16 := by
  have bounded := (status_success_gate hash verify store requested nullifier candidate response success).2.2.2.2.2.2
  unfold partition
  omega

/-- Explicit standard Merkle soundness contract. Presence
requires the exact spent value; absence requires no value at the exact key.
The root identifies a semantic leaf map only under this upstream contract. -/
def MerkleContract (verify : Nat → List Nat → Nat → Bool → Bool)
    (leaves : Nat → List Nat → Option String) : Prop :=
  ∀ root path proof spent, verify root path proof spent = true →
    if spent = true then leaves root path = some spentValue else leaves root path = none

theorem status_merkle_consequence (hash verify leaves store requested nullifier candidate response)
    (merkle : MerkleContract verify leaves)
    (success : status hash verify store requested nullifier candidate = some response) :
    response.boundary = requested ∧
    (if response.spent = true then
      leaves (requested.roots.getD (partition (key hash nullifier)) 0)
        (key hash nullifier) = some spentValue
    else leaves (requested.roots.getD (partition (key hash nullifier)) 0)
        (key hash nullifier) = none) := by
  have checks := status_success_checks hash verify store requested nullifier candidate response success
  exact ⟨checks.2.1, merkle _ _ _ _ checks.2.2⟩

def interrupt (store : Store) : Store := { store with ready := false }

theorem interrupted_status_unavailable (hash verify store requested nullifier candidate) :
    status hash verify (interrupt store) requested nullifier candidate = none := by
  simp [status, ReadGate, interrupt]

theorem stale_boundary_unavailable (hash verify) (store : Store) (requested : Boundary)
    (nullifier candidate)
    (stale : store.boundary ≠ some requested) :
    status hash verify store requested nullifier candidate = none := by
  have blocked : ¬ ReadGate store requested (key hash nullifier) := by
    intro gate
    exact stale gate.2.2.2.1
  simp [status, blocked]

/-- Model completion receives the result of all native recovery checks; true
is not derived from an intent file. Failure keeps the store unavailable. -/
def recoverResult (store : Store) (committed : Boundary) (complete : Bool) : Store :=
  if complete = true then
    { ready := true, healthy := true, actualRoots := committed.roots, boundary := some committed }
  else interrupt store

theorem failed_recovery_unavailable (hash verify store committed requested nullifier candidate) :
    status hash verify (recoverResult store committed false) requested nullifier candidate = none := by
  simp [recoverResult, interrupted_status_unavailable]

theorem recovery_success_read_gate (store : Store) (committed : Boundary) (path : List Nat)
    (roots : committed.roots.length = 16) (width : path.length = 32)
    (byte : path.getD 0 0 < 256) :
    ReadGate (recoverResult store committed true) committed path := by
  change (true : Bool) = true ∧ (true : Bool) = true ∧
    committed.roots = committed.roots ∧ some committed = some committed ∧
    committed.roots.length = 16 ∧ path.length = 32 ∧ path.getD 0 0 < 256
  exact ⟨rfl, rfl, rfl, rfl, roots, width, byte⟩

/-- Query errors (missing publication, capacity, reader, proof or codec failure)
are collapsed to unavailable. Native error categories remain separate. -/
def query (hash : String → Nat → List Nat)
    (verify : Nat → List Nat → Nat → Bool → Bool) (store : Store)
    (published : Option Boundary) (capacity : Bool)
    (nullifier : Nat) (candidate : Option (Bool × Nat)) : Option Status :=
  if capacity = true then
    match published with
    | none => none
    | some boundary => status hash verify store boundary nullifier candidate
  else none

theorem query_success_exact_boundary (hash verify store published capacity nullifier candidate response)
    (success : query hash verify store published capacity nullifier candidate = some response) :
    capacity = true ∧ published = some response.boundary ∧
    ReadGate store response.boundary (key hash nullifier) := by
  by_cases room : capacity = true
  · cases published with
    | none => simp [query, room] at success
    | some boundary =>
        have checked : status hash verify store boundary nullifier candidate = some response := by
          simpa [query, room] using success
        have exactBoundary := (status_success_checks hash verify store boundary nullifier candidate response checked).2.1
        have gate := status_success_gate hash verify store boundary nullifier candidate response checked
        exact ⟨room, by rw [exactBoundary], by rw [exactBoundary]; exact gate⟩
  · simp [query, room] at success

theorem published_pointer_during_interrupt (hash verify store boundary capacity nullifier candidate) :
    query hash verify (interrupt store) (some boundary) capacity nullifier candidate = none := by
  by_cases room : capacity = true
  · simp [query, room, interrupted_status_unavailable]
  · simp [query, room]

structure Snapshot where
  version : Nat
  height : Nat
  applicationRoot : Nat
  boundary : Boundary

structure ExpectedCommit where
  height : Nat
  applicationRoot : Nat
  blockId : List Nat

def PublicationGate (store : Store) (previous : Option Snapshot)
    (next : Snapshot) (expected : ExpectedCommit) : Prop :=
  store.ready = true ∧ store.healthy = true ∧
  store.boundary = some next.boundary ∧ store.actualRoots = next.boundary.roots ∧
  next.boundary.roots.length = 16 ∧ next.height = expected.height ∧
  next.applicationRoot = expected.applicationRoot ∧
  next.boundary.height = some next.height ∧ next.boundary.blockId = expected.blockId ∧
  (match previous with | none => True | some old => old.version ≤ next.version)

instance (store : Store) (previous : Option Snapshot) (next : Snapshot)
    (expected : ExpectedCommit) : Decidable (PublicationGate store previous next expected) := by
  unfold PublicationGate
  cases previous <;> infer_instance

/-- The result of the publication API; a rejection returns no new pointer. -/
def publish (store : Store) (previous : Option Snapshot)
    (next : Snapshot) (expected : ExpectedCommit) : Option Snapshot :=
  if PublicationGate store previous next expected then some next else none

def updatePublished (previous result : Option Snapshot) : Option Snapshot :=
  match result with | none => previous | some next => some next

theorem publication_success_exact (store previous next expected response)
    (success : publish store previous next expected = some response) :
    response = next ∧ PublicationGate store previous next expected := by
  by_cases gate : PublicationGate store previous next expected
  · exact ⟨(Option.some.inj (by simpa [publish, gate] using success)).symm, gate⟩
  · simp [publish, gate] at success

theorem rejected_publication_retains_pointer (store previous next expected)
    (rejected : ¬ PublicationGate store previous next expected) :
    updatePublished previous (publish store previous next expected) = previous := by
  simp [publish, rejected, updatePublished]

/-- Scalar SCT source fast path avoids the reader when already pending. -/
def scalarSpent (pending : Bool) (durable : Option Bool) : Option Bool :=
  if pending = true then some true else durable

/-- Vector SCT source first authenticates every durable result, then ORs
pending membership. An unavailable durable result is not replaced by pending. -/
def vectorSpent (pending : Bool) (durable : Option Bool) : Option Bool :=
  durable.map fun spent => spent || pending

theorem scalar_pending_true (durable) : scalarSpent true durable = some true := rfl

theorem scalar_not_pending (durable) : scalarSpent false durable = durable := rfl

theorem vector_unavailable (pending) : vectorSpent pending none = none := rfl

theorem authenticated_pending_or_durable (pending durable : Bool) :
    vectorSpent pending (some durable) = some (durable || pending) := rfl

theorem authenticated_status_pending_join (hash verify leaves store requested nullifier candidate response)
    (pending : Bool) (merkle : MerkleContract verify leaves)
    (success : status hash verify store requested nullifier candidate = some response) :
    vectorSpent pending ((status hash verify store requested nullifier candidate).map Status.spent) =
      some (response.spent || pending) ∧
    response.boundary = requested ∧
    (if response.spent = true then
      leaves (requested.roots.getD (partition (key hash nullifier)) 0)
        (key hash nullifier) = some spentValue
    else leaves (requested.roots.getD (partition (key hash nullifier)) 0)
        (key hash nullifier) = none) := by
  refine ⟨?_, status_merkle_consequence hash verify leaves store requested nullifier candidate response merkle success⟩
  simp [success, vectorSpent]

set_option pp.all true in
#check @status_success_gate
#print axioms status_success_gate
set_option pp.all true in
#check @status_success_checks
#print axioms status_success_checks
set_option pp.all true in
#check @status_partition_bounded
#print axioms status_partition_bounded
set_option pp.all true in
#check @status_merkle_consequence
#print axioms status_merkle_consequence
set_option pp.all true in
#check @interrupted_status_unavailable
#print axioms interrupted_status_unavailable
set_option pp.all true in
#check @stale_boundary_unavailable
#print axioms stale_boundary_unavailable
set_option pp.all true in
#check @failed_recovery_unavailable
#print axioms failed_recovery_unavailable
set_option pp.all true in
#check @recovery_success_read_gate
#print axioms recovery_success_read_gate
set_option pp.all true in
#check @query_success_exact_boundary
#print axioms query_success_exact_boundary
set_option pp.all true in
#check @published_pointer_during_interrupt
#print axioms published_pointer_during_interrupt
set_option pp.all true in
#check @publication_success_exact
#print axioms publication_success_exact
set_option pp.all true in
#check @rejected_publication_retains_pointer
#print axioms rejected_publication_retains_pointer
set_option pp.all true in
#check @scalar_pending_true
#print axioms scalar_pending_true
set_option pp.all true in
#check @scalar_not_pending
#print axioms scalar_not_pending
set_option pp.all true in
#check @vector_unavailable
#print axioms vector_unavailable
set_option pp.all true in
#check @authenticated_pending_or_durable
#print axioms authenticated_pending_or_durable
set_option pp.all true in
#check @authenticated_status_pending_join
#print axioms authenticated_status_pending_join

end ShielddSecurity.TransferReadback
