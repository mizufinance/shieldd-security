import ShielddSecurity.TransferStageBoundarySource01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBoundaryKeyBinding01
open TransferStateDelta
open TransferReadback (Boundary)
open TransferPreparedAcceptedSource01 (Prepared)
open TransferStageBoundarySource01 (Keys Io)

/-! Generated exact pinned ASCII boundary/legacy key and FORMAT bytes. An
explicit injective key representation derives the three write-key inequalities.
Whole actual stage success derives original serialization and exact boundary,
format and aggregate-root bytes. Hash identity does not certify native getter,
codec, SHA256, finite values, ownership, concurrency or publication semantics. -/

def boundaryBytes : Bytes := [115, 99, 116, 47, 112, 101, 114, 109, 97, 110, 101, 110, 116, 45, 110, 117, 108, 108, 105, 102, 105, 101, 114, 115, 47, 98, 111, 117, 110, 100, 97, 114, 121]

def formatKeyBytes : Bytes := [115, 99, 116, 47, 112, 101, 114, 109, 97, 110, 101, 110, 116, 45, 110, 117, 108, 108, 105, 102, 105, 101, 114, 115, 47, 102, 111, 114, 109, 97, 116]

def rootBytes : Bytes := [115, 99, 116, 47, 112, 101, 114, 109, 97, 110, 101, 110, 116, 45, 110, 117, 108, 108, 105, 102, 105, 101, 114, 115, 47, 114, 111, 111, 116]

def legacyGenerationsBytes : Bytes := [115, 99, 116, 47, 110, 117, 108, 108, 105, 102, 105, 101, 114, 95, 103, 101, 110, 101, 114, 97, 116, 105, 111, 110, 115, 47, 115, 116, 97, 116, 101]

def legacySetRootBytes : Bytes := [115, 99, 116, 47, 110, 117, 108, 108, 105, 102, 105, 101, 114, 95, 115, 101, 116, 47, 114, 111, 111, 116]

def formatValueBytes : Bytes := [115, 104, 105, 101, 108, 100, 100, 46, 110, 111, 109, 116, 46, 115, 112, 101, 110, 116, 46, 118, 49, 46, 115, 104, 97, 50, 53, 54, 46, 112, 49, 54]


def sourceKeys (project : Bytes → Nat) : Keys :=
  ⟨project boundaryBytes, project formatKeyBytes, project rootBytes,
    project legacyGenerationsBytes, project legacySetRootBytes⟩

def sourceIo {O : Type} (io : Io O) : Io O := {io with format := formatValueBytes}

theorem source_write_key_bytes_separate :
    boundaryBytes ≠ rootBytes ∧ boundaryBytes ≠ formatKeyBytes ∧ formatKeyBytes ≠ rootBytes := by decide

theorem projected_source_write_keys_separate (project : Bytes → Nat) (injection : Function.Injective project) :
    (sourceKeys project).boundary ≠ (sourceKeys project).root ∧
      (sourceKeys project).boundary ≠ (sourceKeys project).format ∧
      (sourceKeys project).format ≠ (sourceKeys project).root := by
  exact ⟨fun same => source_write_key_bytes_separate.1 (injection same),
    fun same => source_write_key_bytes_separate.2.1 (injection same),
    fun same => source_write_key_bytes_separate.2.2 (injection same)⟩

theorem source_bound_stage_success_records_exact_serialized_next_format_and_root_bytes {O : Type}
    (io : Io O) (project : Bytes → Nat) (injection : Function.Injective project)
    (state : State O) (prepared : Prepared) (staged : State O)
    (success : TransferStageBoundarySource01.stageBoundary (sourceIo io) (sourceKeys project) state prepared = some staged) :
    TransferStageBoundarySource01.ValidTransition prepared ∧
      TransferStageBoundarySource01.ParentAllowed (sourceIo io) (sourceKeys project) state prepared.previous ∧
      ∃ bytes, io.serialize prepared.next = some bytes ∧
        staged.nonverifiable = state.nonverifiable ∧ staged.objects = state.objects ∧
        staged.verifiable (project boundaryBytes) = some bytes ∧
        staged.verifiable (project formatKeyBytes) = some formatValueBytes ∧
        staged.verifiable (project rootBytes) = some (io.commitment prepared.next.roots) := by
  obtain ⟨valid, parent, bytes, serialized, exactState⟩ :=
    TransferStageBoundarySource01.successful_stage_derives_validation_actual_parent_gate_and_serialized_next
      (sourceIo io) (sourceKeys project) state prepared staged success
  subst staged
  have separate := projected_source_write_keys_separate project injection
  have stored := TransferStageBoundarySource01.separated_boundary_keys_receive_exact_serialized_format_and_commitment_bytes
    (sourceIo io) (sourceKeys project) state prepared.next bytes separate.1 separate.2.1 separate.2.2
  exact ⟨valid, parent, bytes, serialized, rfl, rfl, stored.1, stored.2.1, stored.2.2⟩

set_option pp.all true in
#check @boundaryBytes
#print axioms boundaryBytes

set_option pp.all true in
#check @formatKeyBytes
#print axioms formatKeyBytes

set_option pp.all true in
#check @rootBytes
#print axioms rootBytes

set_option pp.all true in
#check @legacyGenerationsBytes
#print axioms legacyGenerationsBytes

set_option pp.all true in
#check @legacySetRootBytes
#print axioms legacySetRootBytes

set_option pp.all true in
#check @formatValueBytes
#print axioms formatValueBytes

set_option pp.all true in
#check @sourceKeys
#print axioms sourceKeys

set_option pp.all true in
#check @sourceIo
#print axioms sourceIo

set_option pp.all true in
#check @source_write_key_bytes_separate
#print axioms source_write_key_bytes_separate

set_option pp.all true in
#check @projected_source_write_keys_separate
#print axioms projected_source_write_keys_separate

set_option pp.all true in
#check @source_bound_stage_success_records_exact_serialized_next_format_and_root_bytes
#print axioms source_bound_stage_success_records_exact_serialized_next_format_and_root_bytes

end ShielddSecurity.TransferBoundaryKeyBinding01
