import ShielddSecurity.TransferHostSealedCommit01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferHostEndBlock01
open TransferStateDelta
open TransferHostSealedCommit01 (Host)
open TransferWriterPrepareSource01 (Frozen CommitBoundary)
open TransferIndexWriterModel01 (Keys Encoded)
open TransferNullifierBatchSource01 (Pending)

/-! Host::end_block after a successfully checked native i64-to-u64 height.
Actual current height precedes application end_block. Its independently
observed returned state/queue/events precede CommitInterrupted, concrete
take_commit_state, actual block identity and writer.prepare on the exact
transferred state/current pending ordered vector. No desired finalized state
or accepted vector is supplied. Application end_block's flush/component/SCT/
epoch/Arc expect panics are outside this returned-call model. Native signed
height representation, component returned-state/queue semantics, object key/
pending codec/Clone/ownership/snapshots/Host async/locks remain interfaces.
No native/control/full certification or physical rollback from failure. -/

structure ApplicationResult (O E A : Type) where
  state : State O
  queued : List A
  events : List E

structure Io (O E A : Type) where
  currentHeight : State O → Option Nat
  endApplication : Fin (2 ^ 64) → State O → List A → ApplicationResult O E A
  transfer : TransferTakeCommitState01.Io O
  decodePending : O → Pending
  project : Bytes → Nat
  keys : Keys
  convert : A → Option Encoded
  available : Delta O E → Nat → Bool
  deferred : Bool
  exclusive : Bool
  flushHeight : State O → Option Nat
  writer : TransferWriterPrepareSource01.Backend O

structure Outcome (O E A : Type) where
  host : Host O
  queued : List A
  prepared : Option CommitBoundary
  events : List E

def finalized {O E A : Type} (io : Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (queued : List A) : ApplicationResult O E A :=
  io.endApplication height host.active queued

def transferred {O E A : Type} (io : Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (queued : List A) : TransferTakeCommitState01.Outcome O A :=
  let actual := finalized io host height queued
  TransferTakeCommitState01.takeState io.transfer io.decodePending (io.project TransferNullifierObjectKeys01.nullifierBytes)
    io.keys io.convert io.available io.deferred io.exclusive (io.flushHeight actual.state) actual.state actual.queued

def endBlock {O E A : Type} (io : Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (queued : List A) : Outcome O E A :=
  match host.phase with
  | .inBlock =>
    if io.currentHeight host.active = some height.val then
      let taken := transferred io host height queued
      let interrupted := {host with phase := .commitInterrupted, active := taken.active}
      match taken.returned with
      | none => ⟨interrupted, taken.queued, none, []⟩
      | some state => match host.blockId with
        | none => ⟨interrupted, taken.queued, none, []⟩
        | some blockId =>
          let accepted := (TransferBlockPendingSequence01.parentPending io.decodePending io.project state).ordered
          let result := TransferWriterPrepareSource01.prepareWriter io.writer host.writer state height blockId accepted
          match result.returned with
          | none => ⟨{interrupted with writer := result.phase}, taken.queued, none, []⟩
          | some boundary => ⟨{interrupted with phase := .endedBlock, writer := result.phase}, taken.queued, some boundary, (finalized io host height queued).events⟩
    else ⟨host, queued, none, []⟩
  | _ => ⟨host, queued, none, []⟩

theorem actual_height_mismatch_refuses_before_application_and_interruption {O E A : Type}
    (io : Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (queued : List A)
    (inBlock : host.phase = .inBlock) (different : io.currentHeight host.active ≠ some height.val) :
    endBlock io host height queued = ⟨host, queued, none, []⟩ := by
  simp only [endBlock, inBlock, if_neg different]

theorem failed_actual_state_transfer_keeps_host_interrupted_and_transfer_progress {O E A : Type}
    (io : Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (queued : List A)
    (inBlock : host.phase = .inBlock) (sameHeight : io.currentHeight host.active = some height.val)
    (failed : (transferred io host height queued).returned = none) :
    endBlock io host height queued =
      ⟨{host with phase := .commitInterrupted, active := (transferred io host height queued).active},
        (transferred io host height queued).queued, none, []⟩ := by
  simp only [endBlock, inBlock, if_pos sameHeight, failed]

theorem missing_block_identity_refuses_after_actual_state_transfer {O E A : Type}
    (io : Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (queued : List A) (state : State O)
    (inBlock : host.phase = .inBlock) (sameHeight : io.currentHeight host.active = some height.val)
    (taken : (transferred io host height queued).returned = some state) (missing : host.blockId = none) :
    endBlock io host height queued =
      ⟨{host with phase := .commitInterrupted, active := (transferred io host height queued).active},
        (transferred io host height queued).queued, none, []⟩ := by
  simp only [endBlock, inBlock, if_pos sameHeight, taken, missing]

theorem whole_end_block_success_derives_actual_transfer_exact_pending_inputs_and_prepared_owner {O E A : Type}
    (io : Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (queued : List A) (boundary : CommitBoundary)
    (success : (endBlock io host height queued).prepared = some boundary) :
    host.phase = .inBlock ∧ io.currentHeight host.active = some height.val ∧ ∃ state blockId frozen,
      (transferred io host height queued).returned = some state ∧ host.blockId = some blockId ∧
      (TransferWriterPrepareSource01.prepareWriter io.writer host.writer state height blockId
        (TransferBlockPendingSequence01.parentPending io.decodePending io.project state).ordered).returned = some boundary ∧
      (endBlock io host height queued).host.phase = .endedBlock ∧
      (endBlock io host height queued).host.writer = .prepared frozen ∧ boundary = frozen.next ∧
      frozen.insertions.accepted = (TransferBlockPendingSequence01.parentPending io.decodePending io.project state).ordered ∧
      (endBlock io host height queued).host.active = (transferred io host height queued).active ∧
      (endBlock io host height queued).queued = (transferred io host height queued).queued ∧
      (endBlock io host height queued).events = (finalized io host height queued).events := by
  cases phase : host.phase <;> try (simp only [endBlock, phase] at success; cases success)
  by_cases sameHeight : io.currentHeight host.active = some height.val
  · cases taken : (transferred io host height queued).returned with
    | none => simp only [endBlock, phase, if_pos sameHeight, taken] at success; cases success
    | some state =>
      cases block : host.blockId with
      | none => simp only [endBlock, phase, if_pos sameHeight, taken, block] at success; cases success
      | some blockId =>
        let accepted := (TransferBlockPendingSequence01.parentPending io.decodePending io.project state).ordered
        cases preparation : (TransferWriterPrepareSource01.prepareWriter io.writer host.writer state height blockId accepted).returned with
        | none => simp only [endBlock, phase, if_pos sameHeight, taken, block, accepted, preparation] at success; cases success
        | some returned =>
          have same : returned = boundary := Option.some.inj (by
            simpa only [endBlock, phase, if_pos sameHeight, taken, block, accepted, preparation] using success)
          subst returned
          obtain ⟨frozen, _, ready, returnedExact, inputs, _, _⟩ :=
            TransferWriterPrepareSource01.successful_writer_derives_prepared_phase_exact_inputs_and_observed_root
              io.writer host.writer state height blockId accepted boundary preparation
          refine ⟨rfl, sameHeight, state, blockId, frozen, rfl, rfl, preparation, ?_, ?_, returnedExact, inputs, ?_, ?_, ?_⟩
          · simp only [endBlock, phase, if_pos sameHeight, taken, block, accepted, preparation]
          · simpa only [endBlock, phase, if_pos sameHeight, taken, block, accepted, preparation] using ready
          · simp only [endBlock, phase, if_pos sameHeight, taken, block, accepted, preparation]
          · simp only [endBlock, phase, if_pos sameHeight, taken, block, accepted, preparation]
          · simp only [endBlock, phase, if_pos sameHeight, taken, block, accepted, preparation]
  · simp only [endBlock, phase, if_neg sameHeight] at success; cases success

set_option pp.all true in
#check @ApplicationResult
#print axioms ApplicationResult
set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @Outcome
#print axioms Outcome
set_option pp.all true in
#check @finalized
#print axioms finalized
set_option pp.all true in
#check @transferred
#print axioms transferred
set_option pp.all true in
#check @endBlock
#print axioms endBlock
set_option pp.all true in
#check @actual_height_mismatch_refuses_before_application_and_interruption
#print axioms actual_height_mismatch_refuses_before_application_and_interruption
set_option pp.all true in
#check @failed_actual_state_transfer_keeps_host_interrupted_and_transfer_progress
#print axioms failed_actual_state_transfer_keeps_host_interrupted_and_transfer_progress
set_option pp.all true in
#check @missing_block_identity_refuses_after_actual_state_transfer
#print axioms missing_block_identity_refuses_after_actual_state_transfer
set_option pp.all true in
#check @whole_end_block_success_derives_actual_transfer_exact_pending_inputs_and_prepared_owner
#print axioms whole_end_block_success_derives_actual_transfer_exact_pending_inputs_and_prepared_owner
end ShielddSecurity.TransferHostEndBlock01
