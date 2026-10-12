import ShielddSecurity.TransferCheckedWordKnownFinalization01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCheckedWordFreshSnapshot01
open TransferStateDelta (View Writes overlay Delta)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferNullifierBatchSource01 (Backend)
open TransferInjectiveKeyPublication01 (keyCode)
open TransferNullifierObjectKeys01 (nullifierBytes)
open TransferCheckedWordBlockDriver01 (allFields)
open TransferWordSctPendingRead01 (sourceOrdered sourceIsSealed sourceEnsureSealed)
/-! Source Snapshot object_get/object_type return None. StateDelta::new
installs no layers and a live default empty leaf. Their finite source-shaped
object views discharge starting absence for the complete checked-word block
driver. Parent persistent data/reader remains in the supplied backend/child;
this is an ephemeral object initializer, not a durable-data/ICS23 theorem.
Native locks/default-map/Any/compiler/constructor/caller binding stays OPEN;
static source identity is not semantic correspondence or certification. -/

def snapshotObjects {Other : Type} : View (WordTaggedObject Other) := fun _ => none

def emptyLeaf {Other : Type} : Writes (WordTaggedObject Other) := fun _ => none

def runFromSnapshot {O E Other : Type} (backend : Backend O E) (child : Delta O E)
    (batches : List (List CanonicalScalar × Bool)) :
    Except Unit (Except TransferNullifierBatchSource01.BatchError (Writes (WordTaggedObject Other))) :=
  TransferCheckedWordBlockDriver01.run backend child snapshotObjects emptyLeaf (keyCode nullifierBytes) batches

theorem fresh_live_snapshot_constructor_derives_checked_absence_default_and_unsealed_getters {Other : Type} (key : Nat) :
    TransferWordObjectRead01.checkedObject ((overlay (snapshotObjects (Other := Other)) emptyLeaf) key) = .ok none ∧
      TransferWordLayeredObjectRead01.checkedLayers [some (emptyLeaf (Other := Other))] (some snapshotObjects) key = .ok (.opened [] []) ∧
      sourceOrdered ((overlay (snapshotObjects (Other := Other)) emptyLeaf) key) = .ok [] ∧
      sourceIsSealed ((overlay (snapshotObjects (Other := Other)) emptyLeaf) key) = .ok false ∧
      sourceEnsureSealed ((overlay (snapshotObjects (Other := Other)) emptyLeaf) key) = .ok (.ok ()) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem returned_complete_fresh_snapshot_block_derives_exact_actual_global_field_getter {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (batches : List (List CanonicalScalar × Bool))
    (final : Writes (WordTaggedObject Other))
    (returned : runFromSnapshot backend child batches = .ok (.ok final)) :
    (overlay snapshotObjects final) (keyCode nullifierBytes) = some (.inl (.sealed (allFields batches))) ∧
      sourceOrdered ((overlay snapshotObjects final) (keyCode nullifierBytes)) = .ok (allFields batches) ∧
      sourceIsSealed ((overlay snapshotObjects final) (keyCode nullifierBytes)) = .ok true ∧
      sourceEnsureSealed ((overlay snapshotObjects final) (keyCode nullifierBytes)) = .ok (.ok ()) ∧
      (allFields batches).length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
      ((allFields batches).map (fun scalar => TransferScalarLittleEndianBytes01.scalarKey scalar.words)).Nodup ∧
      (∀ nullifier ∈ (allFields batches).map (fun scalar => TransferScalarLittleEndianBytes01.scalarKey scalar.words),
        backend.lookup child nullifier = some false) ∧
      (∀ other, other ≠ keyCode nullifierBytes → final other = none ∧ (overlay snapshotObjects final) other = none) :=
  TransferCheckedWordBlockDriver01.returned_whole_checked_block_derives_actual_exact_original_global_field_getter
    backend child snapshotObjects emptyLeaf final (keyCode nullifierBytes) batches rfl returned

set_option pp.all true in
#check @snapshotObjects
#print axioms snapshotObjects
set_option pp.all true in
#check @emptyLeaf
#print axioms emptyLeaf
set_option pp.all true in
#check @runFromSnapshot
#print axioms runFromSnapshot
set_option pp.all true in
#check @fresh_live_snapshot_constructor_derives_checked_absence_default_and_unsealed_getters
#print axioms fresh_live_snapshot_constructor_derives_checked_absence_default_and_unsealed_getters
set_option pp.all true in
#check @returned_complete_fresh_snapshot_block_derives_exact_actual_global_field_getter
#print axioms returned_complete_fresh_snapshot_block_derives_exact_actual_global_field_getter
end ShielddSecurity.TransferCheckedWordFreshSnapshot01
