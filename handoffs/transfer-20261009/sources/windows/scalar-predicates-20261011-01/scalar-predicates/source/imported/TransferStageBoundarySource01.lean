import ShielddSecurity.TransferStoreCommitSource01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferStageBoundarySource01
open TransferStateDelta
open TransferReadback (Boundary)
open TransferPreparedAcceptedSource01 (Prepared)
open TransferNullifierBatchSource01 (uniqueLoop)
open TransferNullifierConsensusLimits01 (blockCapacity)

/-! Source stage_boundary validates the transition before reading previous
application state. Genesis requires all three boundary keys and both legacy
nullifier keys absent. Later blocks require the actual read_boundary result to
equal previous. Fallible next-boundary serialization precedes exactly three
verifiable writes. Current views, native typed height/root/blockId embedding,
set insertion, read_boundary, static key representation, serialization and
root commitment remain interfaces. No native I/O/publication credit is given.
The height range check models the native u64 domain; it is not a new Rust check.
Pure gate conjunctions do not certify asynchronous read traces or ownership. -/

def initial : Boundary := ⟨none, List.replicate 32 0, List.replicate 16 0⟩

def ValidTransition (prepared : Prepared) : Prop :=
  (match prepared.next.height with
    | none => False
    | some height => height < 2 ^ 64 ∧
        match prepared.previous.height with
        | none => height = 0
        | some earlier => earlier + 1 < 2 ^ 64 ∧ earlier + 1 = height) ∧
    prepared.accepted.length ≤ blockCapacity ∧ uniqueLoop [] prepared.accepted = true ∧
    (prepared.previous.height = none → prepared.previous = initial)

structure Keys where
  boundary : Nat
  format : Nat
  root : Nat
  legacyGenerations : Nat
  legacySetRoot : Nat

structure Io (O : Type) where
  available : State O → Nat → Bool
  readPrevious : State O → Option Boundary
  serialize : Boundary → Option Bytes
  format : Bytes
  commitment : List Nat → Bytes

def InitialAllowed {O : Type} (io : Io O) (keys : Keys) (state : State O) : Prop :=
  io.available state keys.boundary = true ∧ state.verifiable keys.boundary = none ∧
  io.available state keys.format = true ∧ state.verifiable keys.format = none ∧
  io.available state keys.root = true ∧ state.verifiable keys.root = none ∧
  io.available state keys.legacyGenerations = true ∧ state.verifiable keys.legacyGenerations = none ∧
  io.available state keys.legacySetRoot = true ∧ state.verifiable keys.legacySetRoot = none

def ParentAllowed {O : Type} (io : Io O) (keys : Keys) (state : State O) (previous : Boundary) : Prop :=
  match previous.height with
  | none => InitialAllowed io keys state
  | some _ => io.readPrevious state = some previous

def writeBoundary {O : Type} (io : Io O) (keys : Keys) (state : State O) (next : Boundary) (bytes : Bytes) : State O :=
  {state with verifiable := fun other =>
    if other = keys.root then some (io.commitment next.roots)
    else if other = keys.format then some io.format
    else if other = keys.boundary then some bytes
    else state.verifiable other}

def stageBoundary {O : Type} (io : Io O) (keys : Keys) (state : State O) (prepared : Prepared) : Option (State O) := by
  letI : Decidable (ValidTransition prepared) := by
    unfold ValidTransition
    cases prepared.next.height <;> cases prepared.previous.height <;> infer_instance
  letI : Decidable (ParentAllowed io keys state prepared.previous) := by
    unfold ParentAllowed InitialAllowed
    cases prepared.previous.height <;> infer_instance
  exact if ValidTransition prepared then
    if ParentAllowed io keys state prepared.previous then
      (io.serialize prepared.next).map fun bytes => writeBoundary io keys state prepared.next bytes
    else none
  else none

def installStage {O : Type} (backend : TransferWriterPrepareSource01.Backend O) (io : Io O) (keys : Keys) :
    TransferWriterPrepareSource01.Backend O :=
  {backend with stageBoundary := stageBoundary io keys}

theorem boundary_writes_preserve_nonverifiable_objects_and_other_verifiable_keys {O : Type}
    (io : Io O) (keys : Keys) (state : State O) (next : Boundary) (bytes : Bytes) (other : Nat)
    (notRoot : other ≠ keys.root) (notFormat : other ≠ keys.format) (notBoundary : other ≠ keys.boundary) :
    (writeBoundary io keys state next bytes).nonverifiable = state.nonverifiable ∧
      (writeBoundary io keys state next bytes).objects = state.objects ∧
      (writeBoundary io keys state next bytes).verifiable other = state.verifiable other := by
  refine ⟨rfl, rfl, ?_⟩
  simp only [writeBoundary, if_neg notRoot, if_neg notFormat, if_neg notBoundary]

theorem separated_boundary_keys_receive_exact_serialized_format_and_commitment_bytes {O : Type}
    (io : Io O) (keys : Keys) (state : State O) (next : Boundary) (bytes : Bytes)
    (boundaryRoot : keys.boundary ≠ keys.root) (boundaryFormat : keys.boundary ≠ keys.format)
    (formatRoot : keys.format ≠ keys.root) :
    (writeBoundary io keys state next bytes).verifiable keys.boundary = some bytes ∧
      (writeBoundary io keys state next bytes).verifiable keys.format = some io.format ∧
      (writeBoundary io keys state next bytes).verifiable keys.root = some (io.commitment next.roots) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [writeBoundary, if_neg boundaryRoot, if_neg boundaryFormat, if_true]
  · simp only [writeBoundary, if_neg formatRoot, if_true]
  · simp only [writeBoundary, if_true]

theorem successful_stage_derives_validation_actual_parent_gate_and_serialized_next {O : Type}
    (io : Io O) (keys : Keys) (state : State O) (prepared : Prepared) (staged : State O)
    (success : stageBoundary io keys state prepared = some staged) :
    ValidTransition prepared ∧ ParentAllowed io keys state prepared.previous ∧
      ∃ bytes, io.serialize prepared.next = some bytes ∧ staged = writeBoundary io keys state prepared.next bytes := by
  unfold stageBoundary at success
  split at success
  next valid =>
    split at success
    next parent =>
      cases serialized : io.serialize prepared.next with
      | none => simp only [serialized, Option.map_none] at success; contradiction
      | some bytes =>
        have exactState := Option.some.inj (by simpa only [serialized, Option.map_some] using success)
        exact ⟨valid, parent, bytes, rfl, exactState.symm⟩
    next denied => cases success
  next invalid => cases success

theorem existing_boundary_or_legacy_data_refuses_genesis_staging {O : Type}
    (io : Io O) (keys : Keys) (state : State O) (prepared : Prepared)
    (genesis : prepared.previous.height = none)
    (existing : state.verifiable keys.boundary ≠ none ∨ state.verifiable keys.format ≠ none ∨
      state.verifiable keys.root ≠ none ∨ state.verifiable keys.legacyGenerations ≠ none ∨
      state.verifiable keys.legacySetRoot ≠ none) :
    stageBoundary io keys state prepared = none := by
  have denied : ¬ ParentAllowed io keys state prepared.previous := by
    intro parent
    have missing : InitialAllowed io keys state := by simpa only [ParentAllowed, genesis] using parent
    rcases existing with boundary | format | root | generations | setRoot
    · exact boundary missing.2.1
    · exact format missing.2.2.2.1
    · exact root missing.2.2.2.2.2.1
    · exact generations missing.2.2.2.2.2.2.2.1
    · exact setRoot missing.2.2.2.2.2.2.2.2.2
  unfold stageBoundary
  split
  · rfl
  · rfl

theorem successful_store_prepare_derives_stage_validation_with_checked_initial_boundary
    (backend : TransferPreparedAcceptedSource01.Backend) (previous : Boundary)
    (height : Fin (2 ^ 64)) (blockId accepted : List Nat) (prepared : Prepared)
    (initialChecked : previous.height = none → previous = initial)
    (success : TransferPreparedAcceptedSource01.prepare backend previous height blockId accepted = some prepared) :
    ValidTransition prepared := by
  obtain ⟨gate, _, roots, _, previousEq, heightEq, _, _, acceptedEq⟩ :=
    TransferPreparedAcceptedSource01.successful_prepare_derives_gate_and_exact_transition backend previous height blockId accepted prepared success
  unfold ValidTransition
  rw [previousEq, heightEq, acceptedEq]
  refine ⟨⟨height.isLt, ?_⟩, gate.2.2.2.1, gate.2.2.2.2.1, initialChecked⟩
  have consecutive := gate.2.2.2.2.2.2.2
  cases priorHeight : previous.height with
  | none =>
    simp only [TransferPreparedAcceptedSource01.Consecutive, priorHeight] at consecutive
    exact of_decide_eq_true consecutive
  | some earlier =>
    simp only [TransferPreparedAcceptedSource01.Consecutive, priorHeight] at consecutive
    exact of_decide_eq_true consecutive

theorem whole_writer_frozen_success_derives_actual_source_stage_and_application_observation {O : Type}
    (backend : TransferWriterPrepareSource01.Backend O) (io : Io O) (keys : Keys)
    (phase : TransferWriterPrepareSource01.Phase) (state : State O) (height : Fin (2 ^ 64))
    (blockId accepted : List Nat) (frozen : TransferWriterPrepareSource01.Frozen)
    (success : TransferWriterPrepareSource01.prepareFrozen (installStage backend io keys) phase state height blockId accepted = some frozen) :
    ∃ insertions staged bytes,
      insertions.accepted = accepted ∧ ValidTransition insertions ∧ ParentAllowed io keys state insertions.previous ∧
      io.serialize insertions.next = some bytes ∧ staged = writeBoundary io keys state insertions.next bytes ∧
      backend.prepareApplication staged = some frozen.applicationRoot := by
  obtain ⟨previous, insertions, staged, root, _, _, _, stored, stage, application, exactFrozen⟩ :=
    TransferWriterPrepareSource01.successful_frozen_derives_every_prior_call (installStage backend io keys) phase state height blockId accepted frozen success
  have sourceStage : stageBoundary io keys state insertions = some staged := stage
  obtain ⟨valid, parent, bytes, serialized, exactState⟩ :=
    successful_stage_derives_validation_actual_parent_gate_and_serialized_next io keys state insertions staged sourceStage
  obtain ⟨_, _, _, _, _, _, _, _, exactInputs⟩ :=
    TransferPreparedAcceptedSource01.successful_prepare_derives_gate_and_exact_transition backend.store previous.nullifiers height blockId accepted insertions stored
  refine ⟨insertions, staged, bytes, exactInputs, valid, parent, serialized, exactState, ?_⟩
  rw [exactFrozen]
  exact application

set_option pp.all true in
#check @initial
#print axioms initial
set_option pp.all true in
#check @ValidTransition
#print axioms ValidTransition
set_option pp.all true in
#check @Keys
#print axioms Keys
set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @InitialAllowed
#print axioms InitialAllowed
set_option pp.all true in
#check @ParentAllowed
#print axioms ParentAllowed
set_option pp.all true in
#check @writeBoundary
#print axioms writeBoundary
set_option pp.all true in
#check @stageBoundary
#print axioms stageBoundary
set_option pp.all true in
#check @installStage
#print axioms installStage
set_option pp.all true in
#check @boundary_writes_preserve_nonverifiable_objects_and_other_verifiable_keys
#print axioms boundary_writes_preserve_nonverifiable_objects_and_other_verifiable_keys
set_option pp.all true in
#check @separated_boundary_keys_receive_exact_serialized_format_and_commitment_bytes
#print axioms separated_boundary_keys_receive_exact_serialized_format_and_commitment_bytes
set_option pp.all true in
#check @successful_stage_derives_validation_actual_parent_gate_and_serialized_next
#print axioms successful_stage_derives_validation_actual_parent_gate_and_serialized_next
set_option pp.all true in
#check @existing_boundary_or_legacy_data_refuses_genesis_staging
#print axioms existing_boundary_or_legacy_data_refuses_genesis_staging
set_option pp.all true in
#check @successful_store_prepare_derives_stage_validation_with_checked_initial_boundary
#print axioms successful_store_prepare_derives_stage_validation_with_checked_initial_boundary
set_option pp.all true in
#check @whole_writer_frozen_success_derives_actual_source_stage_and_application_observation
#print axioms whole_writer_frozen_success_derives_actual_source_stage_and_application_observation
end ShielddSecurity.TransferStageBoundarySource01
