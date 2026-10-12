import ShielddSecurity.TransferSourceTypedInputProjection01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferFinalizationObjectFrames01
open TransferStateDelta
open TransferNullifierObjectKeys01 (nullifierBytes)
open TransferBoundedNativeCodec01 (ExtendedObject)
open TransferPendingFiniteCodec01 (NativePending)
/-! Known post-seal object mutations include deletion tombstones as well as
SCT tree replacement. Exact pinned key literals are distinct from staged
nullifiers. A finite typed mutation trace invokes existing putObject and
derives pending-object preservation by symbolic induction. No desired final
pending field or per-step output frame is supplied. These cover the six named
SCT/compact/compliance keys only; completeness/order/value and execution of
the native full App finalization trace, all other component effects and
Rust/Any/Clone/Arc/cache/ownership/OS correspondence remain separate. -/

def otherKeys : List Bytes := [[115, 99, 116, 47, 99, 97, 99, 104, 101, 47, 98, 108, 111, 99, 107, 95, 109, 97, 116, 101, 114, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110], [115, 99, 116, 47, 99, 97, 99, 104, 101, 47, 99, 97, 99, 104, 101, 100, 95, 115, 116, 97, 116, 101, 95, 99, 111, 109, 109, 105, 116, 109, 101, 110, 116, 95, 116, 114, 101, 101], [99, 111, 109, 112, 97, 99, 116, 98, 108, 111, 99, 107, 47, 112, 101, 110, 100, 105, 110, 103, 95, 114, 111, 117, 116, 105, 110, 103, 95, 97, 99, 116, 105, 111, 110, 115], [99, 111, 109, 112, 108, 105, 97, 110, 99, 101, 47, 112, 101, 110, 100, 105, 110, 103, 95, 117, 115, 101, 114, 95, 114, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 115], [99, 111, 109, 112, 108, 105, 97, 110, 99, 101, 47, 112, 101, 110, 100, 105, 110, 103, 95, 117, 115, 101, 114, 95, 115, 116, 97, 116, 117, 115, 95, 99, 104, 97, 110, 103, 101, 115], [99, 111, 109, 112, 108, 105, 97, 110, 99, 101, 47, 112, 101, 110, 100, 105, 110, 103, 95, 97, 115, 115, 101, 116, 95, 114, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 115]]

structure Mutation (O : Type) where
  key : Bytes
  permitted : key ∈ otherKeys
  value : Option O

def applyMutation {O E : Type} (project : Bytes → Nat) (delta : Delta O E) (mutation : Mutation O) : Delta O E :=
  putObject delta (project mutation.key) mutation.value

def mutationWalk {O E : Type} (project : Bytes → Nat) : Delta O E → List (Mutation O) → Delta O E
  | delta, [] => delta
  | delta, mutation :: rest => mutationWalk project (applyMutation project delta mutation) rest

theorem source_known_other_object_keys_are_all_separate_from_pending :
    otherKeys.all (fun key => decide (key ≠ nullifierBytes)) = true := by decide

theorem single_known_object_put_or_delete_preserves_pending_observation {O E : Type}
    (project : Bytes → Nat) (injection : Function.Injective project)
    (delta : Delta O E) (mutation : Mutation O) :
    (applyCache (applyMutation project delta mutation).parent (applyMutation project delta mutation).cache).objects
      (project nullifierBytes) = (applyCache delta.parent delta.cache).objects (project nullifierBytes) := by
  have allSeparate : ∀ key ∈ otherKeys, key ≠ nullifierBytes := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using source_known_other_object_keys_are_all_separate_from_pending
  have different : project nullifierBytes ≠ project mutation.key := by
    intro same
    exact allSeparate mutation.key mutation.permitted (injection same.symm)
  exact object_write_frames_other_key delta (project mutation.key) (project nullifierBytes) mutation.value different

theorem symbolic_known_finalization_mutation_walk_preserves_pending_observation {O E : Type}
    (project : Bytes → Nat) (injection : Function.Injective project)
    (delta : Delta O E) (mutations : List (Mutation O)) :
    (applyCache (mutationWalk project delta mutations).parent (mutationWalk project delta mutations).cache).objects
      (project nullifierBytes) = (applyCache delta.parent delta.cache).objects (project nullifierBytes) := by
  induction mutations generalizing delta with
  | nil => rfl
  | cons mutation rest ih =>
    exact (ih (applyMutation project delta mutation)).trans
      (single_known_object_put_or_delete_preserves_pending_observation project injection delta mutation)

theorem known_finalization_mutation_walk_retains_the_same_sealed_native_object {O E : Type}
    (project : Bytes → Nat) (injection : Function.Injective project)
    (encodeNative : NativePending → O) (inputs : List Nat)
    (delta : Delta (ExtendedObject O) E) (mutations : List (Mutation (ExtendedObject O)))
    (sealed : (applyCache delta.parent delta.cache).objects (project nullifierBytes) =
      some (.inl (encodeNative (.sealed inputs)))) :
    (applyCache (mutationWalk project delta mutations).parent (mutationWalk project delta mutations).cache).objects
      (project nullifierBytes) = some (.inl (encodeNative (.sealed inputs))) := by
  exact (symbolic_known_finalization_mutation_walk_preserves_pending_observation project injection delta mutations).trans sealed

set_option pp.all true in
#check @otherKeys
#print axioms otherKeys
set_option pp.all true in
#check @Mutation
#print axioms Mutation
set_option pp.all true in
#check @applyMutation
#print axioms applyMutation
set_option pp.all true in
#check @mutationWalk
#print axioms mutationWalk
set_option pp.all true in
#check @source_known_other_object_keys_are_all_separate_from_pending
#print axioms source_known_other_object_keys_are_all_separate_from_pending
set_option pp.all true in
#check @single_known_object_put_or_delete_preserves_pending_observation
#print axioms single_known_object_put_or_delete_preserves_pending_observation
set_option pp.all true in
#check @symbolic_known_finalization_mutation_walk_preserves_pending_observation
#print axioms symbolic_known_finalization_mutation_walk_preserves_pending_observation
set_option pp.all true in
#check @known_finalization_mutation_walk_retains_the_same_sealed_native_object
#print axioms known_finalization_mutation_walk_retains_the_same_sealed_native_object
end ShielddSecurity.TransferFinalizationObjectFrames01
