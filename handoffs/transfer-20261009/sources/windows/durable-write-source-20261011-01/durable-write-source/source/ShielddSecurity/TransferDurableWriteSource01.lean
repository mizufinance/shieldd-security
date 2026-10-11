import ShielddSecurity.TransferWriterRecoveryJoin01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferDurableWriteSource01
open TransferStateDelta (Bytes)
open TransferPersistIntentSource01 (Filesystem WriteResult)

/-! Source durable_write checks a parent, opens create/truncate/write temporary
file, writes all bytes, syncs that same observed file handle, drops it, renames
temporary to target, then syncs the directory. Every fallible callback carries
independently observed filesystem progress. Drop is a nonfallible ghost of its
observed filesystem effects, not a new native Result call. The final directory
sync may fail after successful rename; failure does not imply an absent target.
Actual path/extension/directory/handle/key/ownership/file/OS durability semantics
and native correspondence remain explicit. No concurrent/native trace proof or
native/control/full Transfer certification is asserted. -/

structure OpenResult where
  observed : Filesystem
  handle : Option Nat

structure Io where
  parentPresent : Bool
  openTemporary : Filesystem → OpenResult
  writeAll : Nat → Bytes → Filesystem → WriteResult
  syncFile : Nat → Filesystem → WriteResult
  closeFile : Nat → Filesystem → Filesystem
  rename : Filesystem → WriteResult
  syncDirectory : Filesystem → WriteResult

def durableWrite (io : Io) (bytes : Bytes) (filesystem : Filesystem) : WriteResult :=
  if io.parentPresent = true then
    let opened := io.openTemporary filesystem
    match opened.handle with
    | none => ⟨opened.observed, false⟩
    | some file =>
      let written := io.writeAll file bytes opened.observed
      if written.succeeded = true then
        let synced := io.syncFile file written.observed
        if synced.succeeded = true then
          let closed := io.closeFile file synced.observed
          let renamed := io.rename closed
          if renamed.succeeded = true then io.syncDirectory renamed.observed else renamed
        else synced
      else written
  else ⟨filesystem, false⟩

def installWrite (intentIo : TransferPersistIntentSource01.Io) (io : Io) : TransferPersistIntentSource01.Io :=
  {intentIo with writeIntent := fun _ bytes filesystem => durableWrite io bytes filesystem}

theorem missing_parent_refuses_before_open_with_original_filesystem (io : Io) (bytes : Bytes) (filesystem : Filesystem)
    (missing : io.parentPresent = false) : durableWrite io bytes filesystem = ⟨filesystem, false⟩ := by
  simp only [durableWrite, missing, Bool.false_eq_true, if_false]

theorem whole_write_success_derives_ordered_calls_and_same_file_handle
    (io : Io) (bytes : Bytes) (filesystem : Filesystem)
    (success : (durableWrite io bytes filesystem).succeeded = true) :
    io.parentPresent = true ∧ ∃ file,
      (io.openTemporary filesystem).handle = some file ∧
      (io.writeAll file bytes (io.openTemporary filesystem).observed).succeeded = true ∧
      (io.syncFile file (io.writeAll file bytes (io.openTemporary filesystem).observed).observed).succeeded = true ∧
      (io.rename (io.closeFile file (io.syncFile file (io.writeAll file bytes (io.openTemporary filesystem).observed).observed).observed)).succeeded = true ∧
      (io.syncDirectory (io.rename (io.closeFile file (io.syncFile file
        (io.writeAll file bytes (io.openTemporary filesystem).observed).observed).observed)).observed).succeeded = true := by
  unfold durableWrite at success
  split at success
  next parent =>
    cases opened : (io.openTemporary filesystem).handle with
    | none => simp only [opened] at success; cases success
    | some file =>
      simp only [opened] at success
      split at success
      next written =>
        split at success
        next synced =>
          split at success
          next renamed => exact ⟨parent, file, rfl, written, synced, renamed, success⟩
          next failed => exact False.elim (failed success)
        next failed => exact False.elim (failed success)
      next failed => exact False.elim (failed success)
  next missing => cases success

theorem failed_directory_sync_after_rename_retains_its_observed_progress
    (io : Io) (bytes : Bytes) (filesystem : Filesystem) (file : Nat)
    (parent : io.parentPresent = true) (opened : (io.openTemporary filesystem).handle = some file)
    (written : (io.writeAll file bytes (io.openTemporary filesystem).observed).succeeded = true)
    (synced : (io.syncFile file (io.writeAll file bytes (io.openTemporary filesystem).observed).observed).succeeded = true)
    (renamed : (io.rename (io.closeFile file (io.syncFile file (io.writeAll file bytes (io.openTemporary filesystem).observed).observed).observed)).succeeded = true)
    (failed : (io.syncDirectory (io.rename (io.closeFile file (io.syncFile file
      (io.writeAll file bytes (io.openTemporary filesystem).observed).observed).observed)).observed).succeeded = false) :
    durableWrite io bytes filesystem = io.syncDirectory (io.rename (io.closeFile file
      (io.syncFile file (io.writeAll file bytes (io.openTemporary filesystem).observed).observed).observed)).observed ∧
      (durableWrite io bytes filesystem).succeeded = false := by
  have exactResult : durableWrite io bytes filesystem = io.syncDirectory (io.rename (io.closeFile file
      (io.syncFile file (io.writeAll file bytes (io.openTemporary filesystem).observed).observed).observed)).observed := by
    simp only [durableWrite, if_pos parent, opened, if_pos written, if_pos synced, if_pos renamed]
  exact ⟨exactResult, by rw [exactResult]; exact failed⟩

theorem installed_failed_write_blocks_intent_readback_and_retains_observed_filesystem
    (intentIo : TransferPersistIntentSource01.Io) (io : Io) (store : TransferReadback.Store)
    (filesystem : Filesystem) (prepared : TransferPreparedAcceptedSource01.Prepared) (bytes : Bytes) (height : Nat)
    (gate : TransferPersistIntentSource01.Gate store prepared) (serialized : intentIo.serialize prepared = some bytes)
    (absent : filesystem.intentExists = false) (nextHeight : prepared.next.height = some height)
    (unretained : filesystem.historyExists height = false) (failed : (durableWrite io bytes filesystem).succeeded = false)
    (hash : String → Nat → List Nat) (verify : Nat → List Nat → Nat → Bool → Bool)
    (requested : TransferReadback.Boundary) (nullifier : Nat) (candidate : Option (Bool × Nat)) :
    (TransferPersistIntentSource01.persistIntent (installWrite intentIo io) store filesystem prepared).returned = false ∧
      (TransferPersistIntentSource01.persistIntent (installWrite intentIo io) store filesystem prepared).store = TransferReadback.interrupt store ∧
      (TransferPersistIntentSource01.persistIntent (installWrite intentIo io) store filesystem prepared).filesystem = (durableWrite io bytes filesystem).observed ∧
      TransferReadback.status hash verify
        (TransferPersistIntentSource01.persistIntent (installWrite intentIo io) store filesystem prepared).store requested nullifier candidate = none := by
  exact TransferPersistIntentSource01.failed_new_write_preserves_observed_filesystem_and_disables_status
    (installWrite intentIo io) store filesystem prepared bytes height gate serialized absent nextHeight unretained failed hash verify requested nullifier candidate

set_option pp.all true in
#check @OpenResult
#print axioms OpenResult
set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @durableWrite
#print axioms durableWrite
set_option pp.all true in
#check @installWrite
#print axioms installWrite
set_option pp.all true in
#check @missing_parent_refuses_before_open_with_original_filesystem
#print axioms missing_parent_refuses_before_open_with_original_filesystem
set_option pp.all true in
#check @whole_write_success_derives_ordered_calls_and_same_file_handle
#print axioms whole_write_success_derives_ordered_calls_and_same_file_handle
set_option pp.all true in
#check @failed_directory_sync_after_rename_retains_its_observed_progress
#print axioms failed_directory_sync_after_rename_retains_its_observed_progress
set_option pp.all true in
#check @installed_failed_write_blocks_intent_readback_and_retains_observed_filesystem
#print axioms installed_failed_write_blocks_intent_readback_and_retains_observed_filesystem
end ShielddSecurity.TransferDurableWriteSource01
