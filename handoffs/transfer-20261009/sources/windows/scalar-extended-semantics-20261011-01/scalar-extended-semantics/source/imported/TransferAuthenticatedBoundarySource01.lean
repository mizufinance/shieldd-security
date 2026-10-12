import ShielddSecurity.TransferBoundaryReaderSource01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferAuthenticatedBoundarySource01
open TransferStateDelta
open TransferReadback (Boundary)
open TransferBoundaryKeyBinding01 (boundaryBytes rootBytes formatKeyBytes)

/-! Source read_committed_boundary compares the actual snapshot root with the
host commitment, verifies each of three actual get_with_proof values, reads
the actual boundary and compares its height to the actual snapshot height.
Proof values and raw read values are separate observations. Binding the latter
to membership needs an explicit immutable snapshot consistency contract and
an independent membership-verifier soundness contract. Neither is an axiom.
Native ICS23/path/spec/finite typed root/height/serde/key/hash/owner/async and
durability correspondence remains explicit. No native/full certification. -/

structure Io (O : Type) where
  snapshotRoot : Option Nat
  getWithProof : Bytes → Option (Bytes × Nat)
  verify : Nat → Bytes → Bytes → Nat → Bool
  height : State O → Option Nat

def authenticateKey {O : Type} (io : Io O) (root : Nat) (key : Bytes) : Bool :=
  match io.getWithProof key with
  | none => false
  | some observed => io.verify root key observed.1 observed.2

def authenticateKeys {O : Type} (io : Io O) (root : Nat) : List Bytes → Bool
  | [] => true
  | key :: rest => if authenticateKey io root key = true then authenticateKeys io root rest else false

def sourceReadKeys : List Bytes := [boundaryBytes, rootBytes, formatKeyBytes]

def readCommittedBoundary {O : Type} (io : Io O) (reader : TransferBoundaryReaderSource01.Io O)
    (project : Bytes → Nat) (state : State O) (root : Nat) : Option Boundary :=
  if io.snapshotRoot = some root then
    if authenticateKeys io root sourceReadKeys = true then
      (TransferBoundaryReaderSource01.readBoundary reader project state).bind fun boundary =>
        (io.height state).bind fun height =>
          if boundary.height = some height then some boundary else none
    else none
  else none

theorem actual_key_authentication_derives_observed_value_proof_and_verifier_success {O : Type}
    (io : Io O) (root : Nat) (key : Bytes) (success : authenticateKey io root key = true) :
    ∃ value proof, io.getWithProof key = some (value, proof) ∧ io.verify root key value proof = true := by
  cases read : io.getWithProof key with
  | none => simp only [authenticateKey, read, Bool.false_eq_true] at success
  | some observed =>
    exact ⟨observed.1, observed.2, rfl, by simpa only [authenticateKey, read] using success⟩

theorem successful_key_walk_derives_each_actual_key_authentication {O : Type}
    (io : Io O) (root : Nat) (keys : List Bytes) (success : authenticateKeys io root keys = true) :
    ∀ key ∈ keys, authenticateKey io root key = true := by
  induction keys with
  | nil => intro key inside; cases inside
  | cons head rest ih =>
    simp only [authenticateKeys] at success
    split at success
    next verified =>
      intro key inside
      cases List.mem_cons.mp inside with
      | inl same => subst key; exact verified
      | inr tail => exact ih success key tail
    next failed => cases success

theorem whole_committed_read_success_derives_actual_snapshot_root_key_checks_boundary_and_height {O : Type}
    (io : Io O) (reader : TransferBoundaryReaderSource01.Io O) (project : Bytes → Nat)
    (state : State O) (root : Nat) (boundary : Boundary)
    (success : readCommittedBoundary io reader project state root = some boundary) :
    io.snapshotRoot = some root ∧ authenticateKeys io root sourceReadKeys = true ∧
      TransferBoundaryReaderSource01.readBoundary reader project state = some boundary ∧
      ∃ height, io.height state = some height ∧ boundary.height = some height := by
  unfold readCommittedBoundary at success
  split at success
  next rootMatches =>
    split at success
    next verified =>
      cases read : TransferBoundaryReaderSource01.readBoundary reader project state with
      | none => simp only [read, Option.bind_none] at success; contradiction
      | some actual =>
        simp only [read, Option.bind_some] at success
        cases height : io.height state with
        | none => simp only [height, Option.bind_none] at success; contradiction
        | some actualHeight =>
          simp only [height, Option.bind_some] at success
          split at success
          next heightMatches =>
            have same : actual = boundary := Option.some.inj success
            subst boundary
            exact ⟨rootMatches, verified, rfl, actualHeight, rfl, heightMatches⟩
          next heightMismatch => cases success
    next unverified => cases success
  next rootMismatch => cases success

theorem whole_committed_read_binds_actual_raw_values_under_snapshot_and_verifier_contracts {O : Type}
    (io : Io O) (reader : TransferBoundaryReaderSource01.Io O) (project : Bytes → Nat)
    (state : State O) (root : Nat) (boundary : Boundary)
    (Member : Nat → Bytes → Bytes → Prop)
    (consistent : ∀ key value proof, io.getWithProof key = some (value, proof) →
      state.verifiable (project key) = some value)
    (sound : ∀ root key value proof, io.verify root key value proof = true → Member root key value)
    (success : readCommittedBoundary io reader project state root = some boundary) :
    ∀ key ∈ sourceReadKeys, ∀ value, state.verifiable (project key) = some value → Member root key value := by
  have returned := whole_committed_read_success_derives_actual_snapshot_root_key_checks_boundary_and_height
    io reader project state root boundary success
  have checked := successful_key_walk_derives_each_actual_key_authentication io root sourceReadKeys returned.2.1
  intro key inside value raw
  obtain ⟨observed, proof, read, verified⟩ :=
    actual_key_authentication_derives_observed_value_proof_and_verifier_success io root key (checked key inside)
  have same : observed = value := Option.some.inj ((consistent key observed proof read).symm.trans raw)
  subst value
  exact sound root key observed proof verified

set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @authenticateKey
#print axioms authenticateKey
set_option pp.all true in
#check @authenticateKeys
#print axioms authenticateKeys
set_option pp.all true in
#check @sourceReadKeys
#print axioms sourceReadKeys
set_option pp.all true in
#check @readCommittedBoundary
#print axioms readCommittedBoundary
set_option pp.all true in
#check @actual_key_authentication_derives_observed_value_proof_and_verifier_success
#print axioms actual_key_authentication_derives_observed_value_proof_and_verifier_success
set_option pp.all true in
#check @successful_key_walk_derives_each_actual_key_authentication
#print axioms successful_key_walk_derives_each_actual_key_authentication
set_option pp.all true in
#check @whole_committed_read_success_derives_actual_snapshot_root_key_checks_boundary_and_height
#print axioms whole_committed_read_success_derives_actual_snapshot_root_key_checks_boundary_and_height
set_option pp.all true in
#check @whole_committed_read_binds_actual_raw_values_under_snapshot_and_verifier_contracts
#print axioms whole_committed_read_binds_actual_raw_values_under_snapshot_and_verifier_contracts
end ShielddSecurity.TransferAuthenticatedBoundarySource01
