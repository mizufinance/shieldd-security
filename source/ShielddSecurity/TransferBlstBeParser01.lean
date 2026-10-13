import ShielddSecurity.TransferBlstByteRoundtrip01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstBeParser01
open TransferBlstByteCaller01 (sourceLEParseStep sourceLEParseMemoryStep sourceLEParseMemory64 sourceScalarLEBytes64)
attribute [local irreducible] sourceLEParseMemoryStep sourceLEParseMemory64 sourceScalarLEBytes64

/-! Exact limbs_from_be_bytes loop for the 32-byte/64-bit-limb route:
remaining n descends from31 to0, the input pointer advances through byte31-n,
and every iteration stores the actual word into limb n/8. Redundant stores
are retained. This derives equivalence to the qualified LE parser on reversed
input, rather than assuming a desired limb output. ABI, restrict/pointer
separation, selected limb width/backend/compiler execution remain separate. -/

def sourceReverseBytes (bytes : Vector UInt8 32) : Vector UInt8 32 :=
  Vector.ofFn (fun index => bytes[31-index.val]'(by have := index.isLt; omega))

theorem reversing_the_actual_32_byte_index_map_twice_restores_every_original_byte
    (bytes : Vector UInt8 32) : sourceReverseBytes (sourceReverseBytes bytes) = bytes := by
  apply Vector.ext
  intro index inside
  simp only [sourceReverseBytes, Vector.getElem_ofFn]
  have restored : 31-(31-index)=index := by omega
  simp only [restored]

def sourceBEParseMemoryStep (bytes : Vector UInt8 32)
    (state : UInt64 × Vector UInt64 4) (remaining : Fin 32) : UInt64 × Vector UInt64 4 :=
  let word := sourceLEParseStep state.1 (bytes[31-remaining.val]'(by have := remaining.isLt; omega))
  (word,state.2.set (remaining.val/8) word (by have := remaining.isLt; omega))

theorem actual_be_pointer_advance_and_redundant_store_are_the_le_step_on_reversed_bytes
    (bytes : Vector UInt8 32) (state : UInt64 × Vector UInt64 4) (remaining : Fin 32) :
    sourceBEParseMemoryStep bytes state remaining =
      sourceLEParseMemoryStep (sourceReverseBytes bytes) state remaining := by
  simp only [sourceBEParseMemoryStep, sourceLEParseMemoryStep, sourceReverseBytes, Vector.getElem_ofFn]

def sourceBEParseMemory64 (bytes : Vector UInt8 32) (initial : Vector UInt64 4) : Vector UInt64 4 :=
  (((List.finRange 32).reverse).foldl (sourceBEParseMemoryStep bytes) (0,initial)).2

theorem actual_be_entire_pointer_and_memory_walk_is_the_qualified_le_walk_on_reversed_bytes
    (bytes : Vector UInt8 32) (initial : Vector UInt64 4) :
    sourceBEParseMemory64 bytes initial = sourceLEParseMemory64 (sourceReverseBytes bytes) initial := by
  unfold sourceBEParseMemory64 sourceLEParseMemory64
  have steps : sourceBEParseMemoryStep bytes = sourceLEParseMemoryStep (sourceReverseBytes bytes) := by
    funext state remaining
    exact actual_be_pointer_advance_and_redundant_store_are_the_le_step_on_reversed_bytes bytes state remaining
  rw [steps]

theorem actual_be_parser_of_actual_reversed_le_writer_recovers_every_original_limb
    (words : Vector UInt64 4) (initial : Vector UInt64 4) :
    sourceBEParseMemory64 (sourceReverseBytes (sourceScalarLEBytes64 words)) initial = words := by
  rw [actual_be_entire_pointer_and_memory_walk_is_the_qualified_le_walk_on_reversed_bytes,
    reversing_the_actual_32_byte_index_map_twice_restores_every_original_byte]
  exact TransferBlstByteRoundtrip01.actual_le_writer_parser_roundtrip_is_the_original_four_limb_vector words initial
set_option pp.all true in
#check @sourceReverseBytes
#print axioms sourceReverseBytes
set_option pp.all true in
#check @reversing_the_actual_32_byte_index_map_twice_restores_every_original_byte
#print axioms reversing_the_actual_32_byte_index_map_twice_restores_every_original_byte
set_option pp.all true in
#check @sourceBEParseMemoryStep
#print axioms sourceBEParseMemoryStep
set_option pp.all true in
#check @actual_be_pointer_advance_and_redundant_store_are_the_le_step_on_reversed_bytes
#print axioms actual_be_pointer_advance_and_redundant_store_are_the_le_step_on_reversed_bytes
set_option pp.all true in
#check @sourceBEParseMemory64
#print axioms sourceBEParseMemory64
set_option pp.all true in
#check @actual_be_entire_pointer_and_memory_walk_is_the_qualified_le_walk_on_reversed_bytes
#print axioms actual_be_entire_pointer_and_memory_walk_is_the_qualified_le_walk_on_reversed_bytes
set_option pp.all true in
#check @actual_be_parser_of_actual_reversed_le_writer_recovers_every_original_limb
#print axioms actual_be_parser_of_actual_reversed_le_writer_recovers_every_original_limb
end ShielddSecurity.TransferBlstBeParser01
