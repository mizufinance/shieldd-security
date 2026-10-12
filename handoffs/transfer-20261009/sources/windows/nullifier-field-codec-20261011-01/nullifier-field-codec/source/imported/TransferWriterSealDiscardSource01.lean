import ShielddSecurity.TransferWriterPrepareSource01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWriterSealDiscardSource01
open TransferWriterPrepareSource01 (CommitBoundary Frozen Phase Outcome)

/-! Source writer seal/discard and committed/status gates. Seal replaces the
phase with Interrupted before the write lock and fallible persist_intent call;
only success sets Sealed. A wrong initial phase is restored. Discard accepts
Prepared only and restores its previous boundary; Sealed cannot discard.
Status first obtains committed and compares both actual boundary fields.
Interrupted owner status is unavailable even if a raw store reader would
still answer. Intent I/O, physical progress, native lock/Clone/Eq/storage
correspondence and raw reader proofs remain interfaces; no durability or
rollback follows from an error. No commit/recovery/native-control credit. -/

structure SealBackend where
  writeLock : Bool
  persistIntent : Frozen → Bool

def committed : Phase → Option CommitBoundary
  | .ready boundary => some boundary
  | .prepared frozen | .sealed frozen => some frozen.previous
  | .interrupted => none

def sealWriter (backend : SealBackend) (phase : Phase) : Outcome :=
  match phase with
  | .prepared frozen =>
    if backend.writeLock = true then
      if backend.persistIntent frozen = true then ⟨.sealed frozen, some frozen.next⟩
      else ⟨.interrupted, none⟩
    else ⟨.interrupted, none⟩
  | _ => ⟨phase, none⟩

def discardWriter : Phase → Phase × Bool
  | .prepared frozen => (.ready frozen.previous, true)
  | phase => (phase, false)

def ownerStatus {R : Type} (phase : Phase) (expected : CommitBoundary) (lookup : CommitBoundary → Option R) : Option R :=
  match committed phase with
  | none => none
  | some actual =>
    if actual.nullifiers = expected.nullifiers ∧ actual.applicationRoot = expected.applicationRoot then lookup expected else none

theorem successful_seal_derives_prepared_lock_intent_and_same_frozen_boundary (backend : SealBackend) (phase : Phase)
    (returned : CommitBoundary) (success : (sealWriter backend phase).returned = some returned) :
    ∃ frozen, phase = .prepared frozen ∧ backend.writeLock = true ∧ backend.persistIntent frozen = true ∧
      (sealWriter backend phase).phase = .sealed frozen ∧ returned = frozen.next := by
  cases phase with
  | ready _ => simp only [sealWriter] at success; contradiction
  | sealed _ => simp only [sealWriter] at success; contradiction
  | interrupted => simp only [sealWriter] at success; contradiction
  | prepared frozen =>
    by_cases locked : backend.writeLock = true
    · by_cases persisted : backend.persistIntent frozen = true
      · have returnedExact : frozen.next = returned := Option.some.inj (by simpa only [sealWriter, if_pos locked, if_pos persisted] using success)
        refine ⟨frozen, rfl, locked, persisted, ?_, returnedExact.symm⟩
        simp only [sealWriter, if_pos locked, if_pos persisted]
      · simp only [sealWriter, if_pos locked, if_neg persisted] at success; contradiction
    · simp only [sealWriter, if_neg locked] at success; contradiction

theorem failed_prepared_seal_interrupts_owner_without_rollback_claim (backend : SealBackend) (frozen : Frozen)
    (failed : (sealWriter backend (.prepared frozen)).returned = none) :
    (sealWriter backend (.prepared frozen)).phase = .interrupted ∧
      committed (sealWriter backend (.prepared frozen)).phase = none := by
  have interrupted : (sealWriter backend (.prepared frozen)).phase = .interrupted := by
    by_cases locked : backend.writeLock = true
    · by_cases persisted : backend.persistIntent frozen = true
      · simp only [sealWriter, if_pos locked, if_pos persisted] at failed; contradiction
      · simp only [sealWriter, if_pos locked, if_neg persisted]
    · simp only [sealWriter, if_neg locked]
  exact ⟨interrupted, by simp only [interrupted, committed]⟩

theorem unprepared_seal_refuses_and_restores_original_phase (backend : SealBackend) (phase : Phase)
    (unprepared : ∀ frozen, phase ≠ .prepared frozen) :
    (sealWriter backend phase).phase = phase ∧ (sealWriter backend phase).returned = none := by
  cases phase with
  | ready _ => exact ⟨rfl, rfl⟩
  | prepared frozen => exact False.elim (unprepared frozen rfl)
  | sealed _ => exact ⟨rfl, rfl⟩
  | interrupted => exact ⟨rfl, rfl⟩

theorem prepared_discard_restores_previous_committed_boundary (frozen : Frozen) :
    discardWriter (.prepared frozen) = (.ready frozen.previous, true) ∧
      committed (discardWriter (.prepared frozen)).1 = some frozen.previous := by
  exact ⟨rfl, rfl⟩

theorem sealed_discard_refuses_and_preserves_previous_committed_boundary (frozen : Frozen) :
    discardWriter (.sealed frozen) = (.sealed frozen, false) ∧
      committed (discardWriter (.sealed frozen)).1 = some frozen.previous := by
  exact ⟨rfl, rfl⟩

theorem interrupted_owner_status_unavailable {R : Type} (expected : CommitBoundary) (lookup : CommitBoundary → Option R) :
    ownerStatus .interrupted expected lookup = none := by
  rfl

theorem successful_owner_status_derives_actual_committed_boundary_and_reader_call {R : Type}
    (phase : Phase) (expected : CommitBoundary) (lookup : CommitBoundary → Option R) (response : R)
    (success : ownerStatus phase expected lookup = some response) :
    ∃ actual, committed phase = some actual ∧ actual.nullifiers = expected.nullifiers ∧
      actual.applicationRoot = expected.applicationRoot ∧ lookup expected = some response := by
  cases observed : committed phase with
  | none => simp only [ownerStatus, observed] at success; contradiction
  | some actual =>
    by_cases matching : actual.nullifiers = expected.nullifiers ∧ actual.applicationRoot = expected.applicationRoot
    · have read : lookup expected = some response := by simpa only [ownerStatus, observed, if_pos matching] using success
      exact ⟨actual, rfl, matching.1, matching.2, read⟩
    · simp only [ownerStatus, observed, if_neg matching] at success; contradiction

theorem whole_successful_prepare_then_seal_retains_exact_frozen_inputs {O : Type}
    (prepareBackend : TransferWriterPrepareSource01.Backend O) (phase : Phase) (state : TransferStateDelta.State O)
    (height : Fin (2 ^ 64)) (blockId accepted : List Nat) (preparedReturned : CommitBoundary)
    (prepareSuccess : (TransferWriterPrepareSource01.prepareWriter prepareBackend phase state height blockId accepted).returned = some preparedReturned)
    (sealBackend : SealBackend) (sealedReturned : CommitBoundary)
    (sealSuccess : (sealWriter sealBackend (TransferWriterPrepareSource01.prepareWriter prepareBackend phase state height blockId accepted).phase).returned = some sealedReturned) :
    ∃ frozen,
      (sealWriter sealBackend (TransferWriterPrepareSource01.prepareWriter prepareBackend phase state height blockId accepted).phase).phase = .sealed frozen ∧
      frozen.insertions.accepted = accepted ∧ sealedReturned = preparedReturned ∧
      sealBackend.writeLock = true ∧ sealBackend.persistIntent frozen = true := by
  obtain ⟨frozen, _, preparedPhase, returnedExact, inputs, _, _⟩ :=
    TransferWriterPrepareSource01.successful_writer_derives_prepared_phase_exact_inputs_and_observed_root
      prepareBackend phase state height blockId accepted preparedReturned prepareSuccess
  have sealCall : (sealWriter sealBackend (.prepared frozen)).returned = some sealedReturned :=
    by simpa only [preparedPhase] using sealSuccess
  obtain ⟨other, initialPhase, locked, persisted, sealedPhase, returnedSeal⟩ :=
    successful_seal_derives_prepared_lock_intent_and_same_frozen_boundary sealBackend (.prepared frozen) sealedReturned sealCall
  have same : frozen = other := Phase.prepared.inj initialPhase
  subst other
  refine ⟨frozen, ?_, inputs, returnedSeal.trans returnedExact.symm, locked, persisted⟩
  simpa only [preparedPhase] using sealedPhase

set_option pp.all true in
#check @SealBackend
#print axioms SealBackend
set_option pp.all true in
#check @committed
#print axioms committed
set_option pp.all true in
#check @sealWriter
#print axioms sealWriter
set_option pp.all true in
#check @discardWriter
#print axioms discardWriter
set_option pp.all true in
#check @ownerStatus
#print axioms ownerStatus
set_option pp.all true in
#check @successful_seal_derives_prepared_lock_intent_and_same_frozen_boundary
#print axioms successful_seal_derives_prepared_lock_intent_and_same_frozen_boundary
set_option pp.all true in
#check @failed_prepared_seal_interrupts_owner_without_rollback_claim
#print axioms failed_prepared_seal_interrupts_owner_without_rollback_claim
set_option pp.all true in
#check @unprepared_seal_refuses_and_restores_original_phase
#print axioms unprepared_seal_refuses_and_restores_original_phase
set_option pp.all true in
#check @prepared_discard_restores_previous_committed_boundary
#print axioms prepared_discard_restores_previous_committed_boundary
set_option pp.all true in
#check @sealed_discard_refuses_and_preserves_previous_committed_boundary
#print axioms sealed_discard_refuses_and_preserves_previous_committed_boundary
set_option pp.all true in
#check @interrupted_owner_status_unavailable
#print axioms interrupted_owner_status_unavailable
set_option pp.all true in
#check @successful_owner_status_derives_actual_committed_boundary_and_reader_call
#print axioms successful_owner_status_derives_actual_committed_boundary_and_reader_call
set_option pp.all true in
#check @whole_successful_prepare_then_seal_retains_exact_frozen_inputs
#print axioms whole_successful_prepare_then_seal_retains_exact_frozen_inputs
end ShielddSecurity.TransferWriterSealDiscardSource01
