import ShielddSecurity.TransferWriterCommitSource01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferPersistIntentSource01
open TransferStateDelta (Bytes)
open TransferReadback (Store Boundary interrupt)
open TransferPreparedAcceptedSource01 (Prepared)

/-! Source Store::persist_intent checks readiness/health, current roots and
boundary, then serializes. Existing intent is idempotent only after an actual
equal record read. New intent requires next height and absent retained history;
ready becomes false before write and true only after returned success.
The callback retains independently observed filesystem progress on failure.
Its Store argument is a ghost of the memory state at the call, erased from
the native durable_write signature; no concurrent native trace is certified.
Serialization/read_record/exists/path/lock/native values and actual durable
write/file/directory semantics remain interfaces. Error never implies an
absent intent, rollback or absence of physical progress. No native/control
or full Transfer certification. -/

structure Filesystem where
  intentExists : Bool
  readIntent : Option Bytes
  historyExists : Nat → Bool

structure WriteResult where
  observed : Filesystem
  succeeded : Bool

structure Io where
  serialize : Prepared → Option Bytes
  writeIntent : Store → Bytes → Filesystem → WriteResult

structure Outcome where
  store : Store
  filesystem : Filesystem
  returned : Bool

def Gate (store : Store) (prepared : Prepared) : Prop :=
  store.ready = true ∧ store.healthy = true ∧ store.actualRoots = prepared.previous.roots ∧ store.boundary = some prepared.previous

def persistIntent (io : Io) (store : Store) (filesystem : Filesystem) (prepared : Prepared) : Outcome := by
  letI : Decidable (Gate store prepared) := by unfold Gate; infer_instance
  exact if Gate store prepared then
    match io.serialize prepared with
    | none => ⟨store, filesystem, false⟩
    | some bytes =>
      if filesystem.intentExists = true then
        ⟨store, filesystem, decide (filesystem.readIntent = some bytes)⟩
      else match prepared.next.height with
        | none => ⟨store, filesystem, false⟩
        | some height =>
          if filesystem.historyExists height = true then ⟨store, filesystem, false⟩
          else
            let observed := io.writeIntent (interrupt store) bytes filesystem
            ⟨{store with ready := observed.succeeded}, observed.observed, observed.succeeded⟩
  else ⟨store, filesystem, false⟩

theorem new_intent_uses_blocked_store_and_retains_observed_write_result (io : Io) (store : Store)
    (filesystem : Filesystem) (prepared : Prepared) (bytes : Bytes) (height : Nat)
    (gate : Gate store prepared) (serialized : io.serialize prepared = some bytes)
    (absent : filesystem.intentExists = false) (nextHeight : prepared.next.height = some height)
    (unretained : filesystem.historyExists height = false) :
    persistIntent io store filesystem prepared =
      ⟨{store with ready := (io.writeIntent (interrupt store) bytes filesystem).succeeded},
        (io.writeIntent (interrupt store) bytes filesystem).observed,
        (io.writeIntent (interrupt store) bytes filesystem).succeeded⟩ := by
  simp only [persistIntent, if_pos gate, serialized, absent, Bool.false_eq_true, if_false, nextHeight, unretained]

theorem existing_equal_intent_is_idempotent_and_preserves_original_observations (io : Io) (store : Store)
    (filesystem : Filesystem) (prepared : Prepared) (bytes : Bytes)
    (gate : Gate store prepared) (serialized : io.serialize prepared = some bytes)
    (present : filesystem.intentExists = true) (equalRead : filesystem.readIntent = some bytes) :
    persistIntent io store filesystem prepared = ⟨store, filesystem, true⟩ := by
  have accepted : decide (filesystem.readIntent = some bytes) = true := decide_eq_true equalRead
  simp only [persistIntent, if_pos gate, serialized, present, if_true, accepted]

theorem existing_unavailable_or_different_intent_refuses_without_ready_change (io : Io) (store : Store)
    (filesystem : Filesystem) (prepared : Prepared) (bytes : Bytes)
    (gate : Gate store prepared) (serialized : io.serialize prepared = some bytes)
    (present : filesystem.intentExists = true) (different : filesystem.readIntent ≠ some bytes) :
    persistIntent io store filesystem prepared = ⟨store, filesystem, false⟩ := by
  have rejected : decide (filesystem.readIntent = some bytes) = false := decide_eq_false different
  simp only [persistIntent, if_pos gate, serialized, present, if_true, rejected]

theorem failed_new_write_preserves_observed_filesystem_and_disables_status
    (io : Io) (store : Store) (filesystem : Filesystem) (prepared : Prepared) (bytes : Bytes) (height : Nat)
    (gate : Gate store prepared) (serialized : io.serialize prepared = some bytes)
    (absent : filesystem.intentExists = false) (nextHeight : prepared.next.height = some height)
    (unretained : filesystem.historyExists height = false)
    (failed : (io.writeIntent (interrupt store) bytes filesystem).succeeded = false)
    (hash : String → Nat → List Nat) (verify : Nat → List Nat → Nat → Bool → Bool)
    (requested : Boundary) (nullifier : Nat) (candidate : Option (Bool × Nat)) :
    (persistIntent io store filesystem prepared).returned = false ∧
      (persistIntent io store filesystem prepared).store = interrupt store ∧
      (persistIntent io store filesystem prepared).filesystem = (io.writeIntent (interrupt store) bytes filesystem).observed ∧
      TransferReadback.status hash verify (persistIntent io store filesystem prepared).store requested nullifier candidate = none := by
  rw [new_intent_uses_blocked_store_and_retains_observed_write_result io store filesystem prepared bytes height gate serialized absent nextHeight unretained]
  refine ⟨failed, ?_, rfl, ?_⟩
  · simp only [failed, interrupt]
  · rw [failed]
    exact TransferReadback.interrupted_status_unavailable hash verify store requested nullifier candidate

set_option pp.all true in
#check @Filesystem
#print axioms Filesystem
set_option pp.all true in
#check @WriteResult
#print axioms WriteResult
set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @Outcome
#print axioms Outcome
set_option pp.all true in
#check @Gate
#print axioms Gate
set_option pp.all true in
#check @persistIntent
#print axioms persistIntent
set_option pp.all true in
#check @new_intent_uses_blocked_store_and_retains_observed_write_result
#print axioms new_intent_uses_blocked_store_and_retains_observed_write_result
set_option pp.all true in
#check @existing_equal_intent_is_idempotent_and_preserves_original_observations
#print axioms existing_equal_intent_is_idempotent_and_preserves_original_observations
set_option pp.all true in
#check @existing_unavailable_or_different_intent_refuses_without_ready_change
#print axioms existing_unavailable_or_different_intent_refuses_without_ready_change
set_option pp.all true in
#check @failed_new_write_preserves_observed_filesystem_and_disables_status
#print axioms failed_new_write_preserves_observed_filesystem_and_disables_status
end ShielddSecurity.TransferPersistIntentSource01
