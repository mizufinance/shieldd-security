import ShielddSecurity.TransferReadback

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferBoundarySourceBridge

open TransferReadback

/-!
Owned three-key authentication and boundary decoding program. Verification
checks bind each supplied proof to the independently selected application root.
Native ICS23 membership soundness and immutable-snapshot proof/raw consistency
are separate contracts. This does not authenticate a local intent or establish
durability from a stored root identifier.
-/

abbrev Bytes := List Nat
def boundaryKey : String := "sct/permanent-nullifiers/boundary"
def rootKey : String := "sct/permanent-nullifiers/root"
def formatKey : String := "sct/permanent-nullifiers/format"
def formatBytes : Bytes :=
  "shieldd.nomt.spent.v1.sha256.p16".toList.map Char.toNat

structure Snapshot where
  root : Nat
  height : Nat
  withProof : String → Option (Bytes × Nat)
  raw : String → Option Bytes

abbrev Verifier := Nat → String → Bytes → Nat → Bool

def checkKey (verify : Verifier) (snapshot : Snapshot) (key : String) : Option Unit :=
  match snapshot.withProof key with
  | none => none
  | some (bytes, proof) =>
      if verify snapshot.root key bytes proof = true then some () else none

theorem checked_key_witness (verify snapshot key)
    (success : checkKey verify snapshot key = some ()) :
    ∃ bytes proof, snapshot.withProof key = some (bytes, proof) ∧
      verify snapshot.root key bytes proof = true := by
  cases found : snapshot.withProof key with
  | none => simp only [checkKey, found] at success; cases success
  | some pair =>
      rcases pair with ⟨bytes, proof⟩
      by_cases valid : verify snapshot.root key bytes proof = true
      · exact ⟨bytes, proof, rfl, valid⟩
      · simp only [checkKey, found, if_neg valid] at success
        cases success

def BoundaryGate (snapshot : Snapshot) (rootsHash : List Nat → Bytes) (boundary : Boundary) : Prop :=
  boundary.height ≠ none ∧ snapshot.raw formatKey = some formatBytes ∧
    snapshot.raw rootKey = some (rootsHash boundary.roots)

instance (snapshot : Snapshot) (rootsHash : List Nat → Bytes) (boundary : Boundary) :
    Decidable (BoundaryGate snapshot rootsHash boundary) := by
  unfold BoundaryGate
  infer_instance

def readBoundary (decode : Bytes → Option Boundary) (rootsHash : List Nat → Bytes)
    (snapshot : Snapshot) : Option Boundary :=
  match snapshot.raw boundaryKey with
  | none => none
  | some bytes => match decode bytes with
    | none => none
    | some boundary => if BoundaryGate snapshot rootsHash boundary then some boundary else none

theorem boundary_read_success (decode rootsHash snapshot boundary)
    (success : readBoundary decode rootsHash snapshot = some boundary) :
    ∃ bytes, snapshot.raw boundaryKey = some bytes ∧ decode bytes = some boundary ∧
      BoundaryGate snapshot rootsHash boundary := by
  cases found : snapshot.raw boundaryKey with
  | none => simp only [readBoundary, found] at success; cases success
  | some bytes =>
      cases decoded : decode bytes with
      | none => simp only [readBoundary, found, decoded] at success; cases success
      | some candidate =>
          by_cases gate : BoundaryGate snapshot rootsHash candidate
          · have same : candidate = boundary := Option.some.inj
              (by simpa only [readBoundary, found, decoded, if_pos gate] using success)
            subst candidate
            exact ⟨bytes, rfl, decoded, gate⟩
          · simp only [readBoundary, found, decoded, if_neg gate] at success
            cases success

def AuthGate (verify : Verifier) (snapshot : Snapshot) (expectedRoot : Nat) : Prop :=
  snapshot.root = expectedRoot ∧
    checkKey verify snapshot boundaryKey = some () ∧
    checkKey verify snapshot rootKey = some () ∧
    checkKey verify snapshot formatKey = some ()

instance (verify : Verifier) (snapshot : Snapshot) (expectedRoot : Nat) :
    Decidable (AuthGate verify snapshot expectedRoot) := by
  unfold AuthGate
  infer_instance

def readCommitted (verify : Verifier) (decode : Bytes → Option Boundary)
    (rootsHash : List Nat → Bytes) (snapshot : Snapshot) (expectedRoot : Nat) : Option Boundary :=
  if AuthGate verify snapshot expectedRoot then
    match readBoundary decode rootsHash snapshot with
    | none => none
    | some boundary => if boundary.height = some snapshot.height then some boundary else none
  else none

theorem committed_read_success (verify decode rootsHash snapshot expectedRoot boundary)
    (success : readCommitted verify decode rootsHash snapshot expectedRoot = some boundary) :
    AuthGate verify snapshot expectedRoot ∧
      readBoundary decode rootsHash snapshot = some boundary ∧
      boundary.height = some snapshot.height := by
  by_cases authenticated : AuthGate verify snapshot expectedRoot
  · cases decoded : readBoundary decode rootsHash snapshot with
    | none => simp only [readCommitted, if_pos authenticated, decoded] at success; cases success
    | some candidate =>
        by_cases height : candidate.height = some snapshot.height
        · have same : candidate = boundary := Option.some.inj
            (by simpa only [readCommitted, if_pos authenticated, decoded, if_pos height] using success)
          subst candidate
          exact ⟨authenticated, rfl, height⟩
        · simp only [readCommitted, if_pos authenticated, decoded, if_neg height] at success
          cases success
  · simp only [readCommitted, if_neg authenticated] at success
    cases success

def MembershipContract (verify : Verifier) (leaves : Nat → String → Option Bytes) : Prop :=
  ∀ root key bytes proof, verify root key bytes proof = true → leaves root key = some bytes

def SnapshotConsistent (snapshot : Snapshot) : Prop :=
  ∀ key bytes proof, snapshot.withProof key = some (bytes, proof) → snapshot.raw key = some bytes

theorem checked_key_raw_membership (verify snapshot key leaves)
    (membership : MembershipContract verify leaves)
    (consistent : SnapshotConsistent snapshot)
    (success : checkKey verify snapshot key = some ()) :
    leaves snapshot.root key = snapshot.raw key := by
  obtain ⟨bytes, proof, found, valid⟩ := checked_key_witness verify snapshot key success
  exact (membership _ _ _ _ valid).trans (consistent _ _ _ found).symm

theorem committed_three_key_membership (verify decode rootsHash snapshot expectedRoot boundary leaves)
    (membership : MembershipContract verify leaves)
    (consistent : SnapshotConsistent snapshot)
    (success : readCommitted verify decode rootsHash snapshot expectedRoot = some boundary) :
    leaves expectedRoot boundaryKey = snapshot.raw boundaryKey ∧
      leaves expectedRoot rootKey = some (rootsHash boundary.roots) ∧
      leaves expectedRoot formatKey = some formatBytes ∧
      boundary.height = some snapshot.height := by
  have checked := committed_read_success _ _ _ _ _ _ success
  obtain ⟨_, _, _, sourceGate⟩ := boundary_read_success _ _ _ _ checked.2.1
  have boundaryMember := checked_key_raw_membership verify snapshot boundaryKey leaves
    membership consistent checked.1.2.1
  have rootsMember := checked_key_raw_membership verify snapshot rootKey leaves
    membership consistent checked.1.2.2.1
  have formatMember := checked_key_raw_membership verify snapshot formatKey leaves
    membership consistent checked.1.2.2.2
  rw [checked.1.1] at boundaryMember rootsMember formatMember
  exact ⟨boundaryMember, rootsMember.trans sourceGate.2.2,
    formatMember.trans sourceGate.2.1, checked.2.2⟩

theorem wrong_application_root_refused (verify decode rootsHash snapshot expectedRoot)
    (wrong : snapshot.root ≠ expectedRoot) :
    readCommitted verify decode rootsHash snapshot expectedRoot = none := by
  have blocked : ¬ AuthGate verify snapshot expectedRoot := fun gate => wrong gate.1
  simp only [readCommitted, if_neg blocked]

theorem missing_format_refused (decode rootsHash snapshot)
    (missing : snapshot.raw formatKey = none) :
    readBoundary decode rootsHash snapshot = none := by
  cases found : snapshot.raw boundaryKey with
  | none => simp only [readBoundary, found]
  | some bytes =>
      cases decoded : decode bytes with
      | none => simp only [readBoundary, found, decoded]
      | some boundary =>
          have blocked : ¬ BoundaryGate snapshot rootsHash boundary := by
            intro gate
            have impossible : (none : Option Bytes) = some formatBytes := missing.symm.trans gate.2.1
            cases impossible
          simp only [readBoundary, found, decoded, if_neg blocked]

set_option pp.all true in
#check @checked_key_witness
#print axioms checked_key_witness
set_option pp.all true in
#check @boundary_read_success
#print axioms boundary_read_success
set_option pp.all true in
#check @committed_read_success
#print axioms committed_read_success
set_option pp.all true in
#check @checked_key_raw_membership
#print axioms checked_key_raw_membership
set_option pp.all true in
#check @committed_three_key_membership
#print axioms committed_three_key_membership
set_option pp.all true in
#check @wrong_application_root_refused
#print axioms wrong_application_root_refused
set_option pp.all true in
#check @missing_format_refused
#print axioms missing_format_refused

end ShielddSecurity.TransferBoundarySourceBridge
