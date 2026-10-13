import ShielddSecurity.TransferBlstParserState01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstParserSchedule01
open TransferBlstByteCaller01 (sourceLEParseMemoryStep sourceLEParseMemory64)
open TransferBlstParserState01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarLittleEndianBytes01 (decodeLE)

def sourceMemoryWalk (bytes : Vector UInt8 32) :
    (count : Nat) → count ≤ 32 → UInt64 × Vector UInt64 4 → UInt64 × Vector UInt64 4
  | 0, _, state => state
  | count+1, inside, state =>
      sourceMemoryWalk bytes count (by omega)
        (sourceLEParseMemoryStep bytes state ⟨count,by omega⟩)

theorem symbolic_memory_walk_completes_every_parser_frontier
    (bytes : Vector UInt8 32) (count : Nat) (inside : count ≤ 32)
    (state : UInt64 × Vector UInt64 4) (ready : FrontierInvariant bytes count state) :
    FrontierInvariant bytes 0 (sourceMemoryWalk bytes count inside state) := by
  induction count generalizing state with
  | zero => exact ready
  | succ count ih =>
    exact ih (by omega) _
      (actual_parser_step_derives_both_word_and_completed_limb_rows bytes ⟨count,by omega⟩ state ready)

def sourceDescendingIndices (count : Nat) (inside : count ≤ 32) : List (Fin 32) :=
  (List.finRange count).reverse.map (fun index => ⟨index.val,by have := index.isLt; omega⟩)

theorem actual_descending_index_schedule_has_the_symbolic_last_index_recurrence
    (count : Nat) (inside : count+1 ≤ 32) :
    sourceDescendingIndices (count+1) inside =
      ⟨count,by omega⟩ :: sourceDescendingIndices count (by omega) := by
  unfold sourceDescendingIndices
  rw [List.finRange_succ_last,List.reverse_append]
  simp only [List.reverse_singleton,List.map_cons,List.singleton_append]
  rw [← List.map_reverse,List.map_map]
  rfl

theorem symbolic_memory_walk_is_the_actual_descending_index_fold
    (bytes : Vector UInt8 32) (count : Nat) (inside : count ≤ 32)
    (state : UInt64 × Vector UInt64 4) :
    sourceMemoryWalk bytes count inside state =
      (sourceDescendingIndices count inside).foldl (sourceLEParseMemoryStep bytes) state := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    rw [actual_descending_index_schedule_has_the_symbolic_last_index_recurrence,List.foldl_cons]
    exact ih (by omega) _

theorem actual_full_32_byte_schedule_is_the_exact_fin32_reverse :
    sourceDescendingIndices 32 (by decide) = (List.finRange 32).reverse := by
  change (List.finRange 32).reverse.map id = (List.finRange 32).reverse
  exact List.map_id _

theorem actual_parser_every_limb_is_the_reconstructed_byte_suffix
    (bytes : Vector UInt8 32) (initialBuffer : Vector UInt64 4) (limb : Fin 4) :
    (sourceLEParseMemory64 bytes initialBuffer)[limb.val].toNat =
      decodeLE (bytes.toList.drop (8*limb.val)) % radix64 := by
  have completed := symbolic_memory_walk_completes_every_parser_frontier bytes 32 (by decide)
    (0,initialBuffer) (actual_parser_initial_memory_derives_the_frontier_invariant bytes initialBuffer)
  rw [symbolic_memory_walk_is_the_actual_descending_index_fold,
    actual_full_32_byte_schedule_is_the_exact_fin32_reverse] at completed
  exact completed.2 limb (Nat.zero_le _)
set_option pp.all true in
#check @sourceMemoryWalk
#print axioms sourceMemoryWalk
set_option pp.all true in
#check @symbolic_memory_walk_completes_every_parser_frontier
#print axioms symbolic_memory_walk_completes_every_parser_frontier
set_option pp.all true in
#check @sourceDescendingIndices
#print axioms sourceDescendingIndices
set_option pp.all true in
#check @actual_descending_index_schedule_has_the_symbolic_last_index_recurrence
#print axioms actual_descending_index_schedule_has_the_symbolic_last_index_recurrence
set_option pp.all true in
#check @symbolic_memory_walk_is_the_actual_descending_index_fold
#print axioms symbolic_memory_walk_is_the_actual_descending_index_fold
set_option pp.all true in
#check @actual_full_32_byte_schedule_is_the_exact_fin32_reverse
#print axioms actual_full_32_byte_schedule_is_the_exact_fin32_reverse
set_option pp.all true in
#check @actual_parser_every_limb_is_the_reconstructed_byte_suffix
#print axioms actual_parser_every_limb_is_the_reconstructed_byte_suffix
end ShielddSecurity.TransferBlstParserSchedule01
