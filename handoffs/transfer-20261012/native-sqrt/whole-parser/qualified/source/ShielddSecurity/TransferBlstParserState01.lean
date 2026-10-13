import ShielddSecurity.TransferBlstParserValue01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstParserState01
open TransferBlstByteCaller01 (sourceLEParseStep sourceLEParseMemoryStep)
open TransferBlstParserValue01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarLittleEndianBytes01 (decodeLE)

def FrontierInvariant (bytes : Vector UInt8 32) (frontier : Nat)
    (state : UInt64 × Vector UInt64 4) : Prop :=
  state.1.toNat = decodeLE (bytes.toList.drop frontier) % radix64 ∧
  ∀ limb : Fin 4, frontier ≤ 8*limb.val →
    state.2[limb.val].toNat = decodeLE (bytes.toList.drop (8*limb.val)) % radix64

theorem actual_parser_initial_memory_derives_the_frontier_invariant
    (bytes : Vector UInt8 32) (initialBuffer : Vector UInt64 4) :
    FrontierInvariant bytes 32 (0,initialBuffer) := by
  constructor
  · have width : bytes.toList.length = 32 := by simp
    have empty : bytes.toList.drop 32 = [] := List.drop_eq_nil_of_le (Nat.le_of_eq width)
    change (0 : UInt64).toNat = decodeLE (bytes.toList.drop 32) % radix64
    rw [empty]
    rfl
  · intro limb complete
    have := limb.isLt
    omega

theorem actual_descending_parser_step_derives_the_next_word_value
    (bytes : Vector UInt8 32) (index : Fin 32) (state : UInt64 × Vector UInt64 4)
    (meaning : state.1.toNat = decodeLE (bytes.toList.drop (index.val+1)) % radix64) :
    (sourceLEParseStep state.1 bytes[index.val]).toNat =
      decodeLE (bytes.toList.drop index.val) % radix64 := by
  have split : bytes.toList.drop index.val = bytes[index.val] :: bytes.toList.drop (index.val+1) := by
    simpa only [Vector.getElem_toList] using
      List.drop_eq_getElem_cons (by simpa only [Vector.length_toList] using index.isLt : index.val < bytes.toList.length)
  rw [actual_shift_or_parser_step_has_the_exact_full_wrapped_integer_value,meaning,
    Nat.add_mod,Nat.mod_mul_mod,← Nat.add_mod,split,decodeLE]
  congr 1
  omega

theorem actual_parser_step_derives_both_word_and_completed_limb_rows
    (bytes : Vector UInt8 32) (index : Fin 32) (state : UInt64 × Vector UInt64 4)
    (ready : FrontierInvariant bytes (index.val+1) state) :
    FrontierInvariant bytes index.val (sourceLEParseMemoryStep bytes state index) := by
  have word := actual_descending_parser_step_derives_the_next_word_value bytes index state ready.1
  constructor
  · exact word
  · intro limb complete
    dsimp only [sourceLEParseMemoryStep]
    by_cases stored : index.val/8 = limb.val
    · have boundary : index.val = 8*limb.val := by omega
      rw [Vector.getElem_set,if_pos stored,word,boundary]
    · rw [Vector.getElem_set,if_neg stored]
      exact ready.2 limb (by omega)
set_option pp.all true in
#check @FrontierInvariant
#print axioms FrontierInvariant
set_option pp.all true in
#check @actual_parser_initial_memory_derives_the_frontier_invariant
#print axioms actual_parser_initial_memory_derives_the_frontier_invariant
set_option pp.all true in
#check @actual_descending_parser_step_derives_the_next_word_value
#print axioms actual_descending_parser_step_derives_the_next_word_value
set_option pp.all true in
#check @actual_parser_step_derives_both_word_and_completed_limb_rows
#print axioms actual_parser_step_derives_both_word_and_completed_limb_rows
end ShielddSecurity.TransferBlstParserState01
