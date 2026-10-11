import ShielddSecurity.TransferBoundaryKeyBinding01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBoundaryReaderSource01
open TransferStateDelta
open TransferReadback (Boundary)
open TransferPreparedAcceptedSource01 (Prepared)
open TransferBoundaryKeyBinding01 (boundaryBytes formatKeyBytes rootBytes formatValueBytes sourceKeys)

/-! Source read_boundary requires actual available boundary bytes, native FORMAT,
successful serde decode, a present decoded height and exact roots commitment
bytes. Missing state is unavailable, never a default or empty commitment.
The reader is installed into the previously qualified stage program, deriving
the previous state's actual format/root checks for noninitial stage success.
Native fixed-width values/key projection/current view/raw availability/serde
and roots commitment/async ownership remain primitive correspondence interfaces.
This read is not an independent ICS23 authentication proof or publication result.
No native/control/full Transfer certification. -/

structure Io (O : Type) where
  available : State O → Nat → Bool
  decode : Bytes → Option Boundary
  commitment : List Nat → Bytes

def readBoundary {O : Type} (io : Io O) (project : Bytes → Nat) (state : State O) : Option Boundary :=
  if io.available state (project boundaryBytes) = true then
    (state.verifiable (project boundaryBytes)).bind fun bytes =>
      if io.available state (project formatKeyBytes) = true ∧
          state.verifiable (project formatKeyBytes) = some formatValueBytes then
        (io.decode bytes).bind fun boundary =>
          if boundary.height.isSome = true then
            if io.available state (project rootBytes) = true ∧
                state.verifiable (project rootBytes) = some (io.commitment boundary.roots) then some boundary
            else none
          else none
      else none
  else none

def installReader {O : Type} (stage : TransferStageBoundarySource01.Io O) (io : Io O) (project : Bytes → Nat) :
    TransferStageBoundarySource01.Io O :=
  {stage with available := io.available, readPrevious := readBoundary io project,
    format := formatValueBytes, commitment := io.commitment}

theorem successful_boundary_read_derives_actual_bytes_format_decode_height_and_roots {O : Type}
    (io : Io O) (project : Bytes → Nat) (state : State O) (boundary : Boundary)
    (success : readBoundary io project state = some boundary) :
    ∃ bytes, io.available state (project boundaryBytes) = true ∧
      state.verifiable (project boundaryBytes) = some bytes ∧
      io.available state (project formatKeyBytes) = true ∧
      state.verifiable (project formatKeyBytes) = some formatValueBytes ∧
      io.decode bytes = some boundary ∧ boundary.height.isSome = true ∧
      io.available state (project rootBytes) = true ∧
      state.verifiable (project rootBytes) = some (io.commitment boundary.roots) := by
  unfold readBoundary at success
  split at success
  next available =>
    cases read : state.verifiable (project boundaryBytes) with
    | none => simp only [read, Option.bind_none] at success; contradiction
    | some bytes =>
      simp only [read, Option.bind_some] at success
      split at success
      next format =>
        cases decoded : io.decode bytes with
        | none => simp only [decoded, Option.bind_none] at success; contradiction
        | some actual =>
          simp only [decoded, Option.bind_some] at success
          split at success
          next height =>
            split at success
            next roots =>
              have same : actual = boundary := Option.some.inj success
              subst boundary
              exact ⟨bytes, available, rfl, format.1, format.2, decoded, height, roots.1, roots.2⟩
            next unavailable => cases success
          next noHeight => cases success
      next wrongFormat => cases success
  next unavailable => cases success

theorem missing_boundary_refuses_without_default {O : Type}
    (io : Io O) (project : Bytes → Nat) (state : State O)
    (missing : state.verifiable (project boundaryBytes) = none) :
    readBoundary io project state = none := by
  unfold readBoundary
  split
  · rw [missing]
    rfl
  · rfl

theorem wrong_format_refuses_before_decoded_boundary {O : Type}
    (io : Io O) (project : Bytes → Nat) (state : State O)
    (wrong : state.verifiable (project formatKeyBytes) ≠ some formatValueBytes) :
    readBoundary io project state = none := by
  have denied : ¬ (io.available state (project formatKeyBytes) = true ∧
      state.verifiable (project formatKeyBytes) = some formatValueBytes) := fun checked => wrong checked.2
  unfold readBoundary
  split
  · cases state.verifiable (project boundaryBytes) with
    | none => rfl
    | some bytes =>
      simp only [Option.bind_some, if_neg denied]
  · rfl

theorem successful_noninitial_source_stage_derives_previous_application_format_and_root_bytes {O : Type}
    (stage : TransferStageBoundarySource01.Io O) (io : Io O) (project : Bytes → Nat)
    (state : State O) (prepared : Prepared) (staged : State O)
    (noninitial : prepared.previous.height.isSome = true)
    (success : TransferStageBoundarySource01.stageBoundary (installReader stage io project) (sourceKeys project) state prepared = some staged) :
    TransferStageBoundarySource01.ValidTransition prepared ∧
      ∃ bytes, io.available state (project boundaryBytes) = true ∧
        state.verifiable (project boundaryBytes) = some bytes ∧
        io.available state (project formatKeyBytes) = true ∧
        state.verifiable (project formatKeyBytes) = some formatValueBytes ∧
        io.decode bytes = some prepared.previous ∧
        io.available state (project rootBytes) = true ∧
        state.verifiable (project rootBytes) = some (io.commitment prepared.previous.roots) := by
  obtain ⟨valid, parent, _, _, _⟩ :=
    TransferStageBoundarySource01.successful_stage_derives_validation_actual_parent_gate_and_serialized_next
      (installReader stage io project) (sourceKeys project) state prepared staged success
  have reader : readBoundary io project state = some prepared.previous := by
    cases height : prepared.previous.height with
    | none => cases noninitial
    | some actual =>
      simpa only [TransferStageBoundarySource01.ParentAllowed, height, installReader] using parent
  obtain ⟨bytes, available, raw, formatAvailable, format, decoded, _, rootsAvailable, roots⟩ :=
    successful_boundary_read_derives_actual_bytes_format_decode_height_and_roots io project state prepared.previous reader
  exact ⟨valid, bytes, available, raw, formatAvailable, format, decoded, rootsAvailable, roots⟩

set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @readBoundary
#print axioms readBoundary
set_option pp.all true in
#check @installReader
#print axioms installReader
set_option pp.all true in
#check @successful_boundary_read_derives_actual_bytes_format_decode_height_and_roots
#print axioms successful_boundary_read_derives_actual_bytes_format_decode_height_and_roots
set_option pp.all true in
#check @missing_boundary_refuses_without_default
#print axioms missing_boundary_refuses_without_default
set_option pp.all true in
#check @wrong_format_refuses_before_decoded_boundary
#print axioms wrong_format_refuses_before_decoded_boundary
set_option pp.all true in
#check @successful_noninitial_source_stage_derives_previous_application_format_and_root_bytes
#print axioms successful_noninitial_source_stage_derives_previous_application_format_and_root_bytes
end ShielddSecurity.TransferBoundaryReaderSource01
