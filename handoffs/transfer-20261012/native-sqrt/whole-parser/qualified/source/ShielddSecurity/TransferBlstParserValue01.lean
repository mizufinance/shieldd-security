import ShielddSecurity.TransferBlstByteCaller01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstParserValue01
open TransferBlstByteCaller01 (sourceLEParseStep sourceLEParseMemoryStep sourceLEParseMemory64)
open TransferScalarSerializationRange01 (radix64)
open TransferScalarLittleEndianBytes01 (decodeLE)

theorem actual_shift_or_parser_step_has_the_exact_full_wrapped_integer_value
    (word : UInt64) (byte : UInt8) :
    (sourceLEParseStep word byte).toNat = (word.toNat*256+byte.toNat)%radix64 := by
  unfold sourceLEParseStep
  rw [UInt64.toNat_or,UInt64.toNat_shiftLeft,UInt64.toNat_ofNat']
  change (word.toNat <<< 8 % 2^64) ||| (byte.toNat % 2^64) =
    (word.toNat*256+byte.toNat)%2^64
  rw [← Nat.or_mod_two_pow,
    ← Nat.shiftLeft_add_eq_or_of_lt (i:=8) byte.toNat_lt word.toNat,Nat.shiftLeft_eq]

def sourceReverseParserWord (bytes : List UInt8) (seed : UInt64) : UInt64 :=
  bytes.reverse.foldl sourceLEParseStep seed

theorem symbolic_reverse_parser_word_recurrence_derives_the_full_integer_prefix
    (bytes : List UInt8) (seed : UInt64) :
    (sourceReverseParserWord bytes seed).toNat =
      (decodeLE bytes+256^bytes.length*seed.toNat)%radix64 := by
  induction bytes generalizing seed with
  | nil =>
    have bound : seed.toNat < radix64 := seed.toNat_lt
    simp only [sourceReverseParserWord,List.reverse_nil,List.foldl_nil,decodeLE,List.length_nil,
      Nat.pow_zero,Nat.one_mul,Nat.zero_add,Nat.mod_eq_of_lt bound]
  | cons byte rest ih =>
    unfold sourceReverseParserWord
    rw [List.reverse_cons,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    change (sourceLEParseStep (sourceReverseParserWord rest seed) byte).toNat = _
    rw [actual_shift_or_parser_step_has_the_exact_full_wrapped_integer_value,ih]
    have positional : (decodeLE rest+256^rest.length*seed.toNat)*256+byte.toNat =
        decodeLE (byte::rest)+256^(byte::rest).length*seed.toNat := by
      simp only [decodeLE,List.length_cons,Nat.pow_succ]
      ring
    calc
      _ = ((decodeLE rest+256^rest.length*seed.toNat)*256+byte.toNat)%radix64 := by
        rw [Nat.add_mod,Nat.mod_mul_mod,← Nat.add_mod]
      _ = _ := by rw [positional]

theorem actual_zero_seed_reverse_parser_word_is_the_low_64_bits_of_all_input_bytes
    (bytes : List UInt8) :
    (sourceReverseParserWord bytes 0).toNat = decodeLE bytes % radix64 := by
  rw [symbolic_reverse_parser_word_recurrence_derives_the_full_integer_prefix]
  simp only [UInt64.toNat_zero,Nat.mul_zero,Nat.add_zero]

theorem source_parser_memory_fold_word_projects_to_the_actual_byte_word_fold
    (bytes : Vector UInt8 32) (indices : List (Fin 32)) (state : UInt64 × Vector UInt64 4) :
    (indices.foldl (sourceLEParseMemoryStep bytes) state).1 =
      (indices.map (fun index => bytes[index.val])).foldl sourceLEParseStep state.1 := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
    rw [List.foldl_cons,List.map_cons,List.foldl_cons,ih]
    rfl

theorem actual_descending_index_data_is_the_reversed_input_byte_array (bytes : Vector UInt8 32) :
    ((List.finRange 32).reverse.map (fun index => bytes[index.val])) = bytes.toList.reverse := by
  have forward : (List.finRange 32).map (fun index => bytes[index.val]) = bytes.toList := by
    apply List.ext_getElem
    · simp
    · intro index leftBound rightBound
      simp
  rw [List.map_reverse,forward]

def sourceActualParserFinalState (bytes : Vector UInt8 32) (initialBuffer : Vector UInt64 4) :
    UInt64 × Vector UInt64 4 :=
  (List.finRange 32).reverse.foldl (sourceLEParseMemoryStep bytes) (0,initialBuffer)

theorem actual_parser_final_word_derives_the_low_64_bits_of_the_input_byte_array
    (bytes : Vector UInt8 32) (initialBuffer : Vector UInt64 4) :
    (sourceActualParserFinalState bytes initialBuffer).1.toNat = decodeLE bytes.toList % radix64 := by
  unfold sourceActualParserFinalState
  rw [source_parser_memory_fold_word_projects_to_the_actual_byte_word_fold,
    actual_descending_index_data_is_the_reversed_input_byte_array]
  exact actual_zero_seed_reverse_parser_word_is_the_low_64_bits_of_all_input_bytes _

theorem actual_parser_final_store_contains_the_exact_final_word
    (bytes : Vector UInt8 32) (initialBuffer : Vector UInt64 4) :
    (sourceLEParseMemory64 bytes initialBuffer)[0] =
      (sourceActualParserFinalState bytes initialBuffer).1 := by
  have lastStore : ∀ state : UInt64 × Vector UInt64 4,
      (sourceLEParseMemoryStep bytes state ⟨0,by decide⟩).2[0] =
        (sourceLEParseMemoryStep bytes state ⟨0,by decide⟩).1 := by
    intro state
    simp only [sourceLEParseMemoryStep,Vector.getElem_set_self]
  unfold sourceLEParseMemory64 sourceActualParserFinalState
  rw [List.finRange_succ,List.reverse_cons,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil]
  exact lastStore _

theorem actual_memory_parser_derives_the_entire_low_word_from_every_input_byte_array
    (bytes : Vector UInt8 32) (initialBuffer : Vector UInt64 4) :
    (sourceLEParseMemory64 bytes initialBuffer)[0].toNat = decodeLE bytes.toList % radix64 := by
  rw [actual_parser_final_store_contains_the_exact_final_word,
    actual_parser_final_word_derives_the_low_64_bits_of_the_input_byte_array]
set_option pp.all true in
#check @actual_shift_or_parser_step_has_the_exact_full_wrapped_integer_value
#print axioms actual_shift_or_parser_step_has_the_exact_full_wrapped_integer_value
set_option pp.all true in
#check @sourceReverseParserWord
#print axioms sourceReverseParserWord
set_option pp.all true in
#check @symbolic_reverse_parser_word_recurrence_derives_the_full_integer_prefix
#print axioms symbolic_reverse_parser_word_recurrence_derives_the_full_integer_prefix
set_option pp.all true in
#check @actual_zero_seed_reverse_parser_word_is_the_low_64_bits_of_all_input_bytes
#print axioms actual_zero_seed_reverse_parser_word_is_the_low_64_bits_of_all_input_bytes
set_option pp.all true in
#check @source_parser_memory_fold_word_projects_to_the_actual_byte_word_fold
#print axioms source_parser_memory_fold_word_projects_to_the_actual_byte_word_fold
set_option pp.all true in
#check @actual_descending_index_data_is_the_reversed_input_byte_array
#print axioms actual_descending_index_data_is_the_reversed_input_byte_array
set_option pp.all true in
#check @sourceActualParserFinalState
#print axioms sourceActualParserFinalState
set_option pp.all true in
#check @actual_parser_final_word_derives_the_low_64_bits_of_the_input_byte_array
#print axioms actual_parser_final_word_derives_the_low_64_bits_of_the_input_byte_array
set_option pp.all true in
#check @actual_parser_final_store_contains_the_exact_final_word
#print axioms actual_parser_final_store_contains_the_exact_final_word
set_option pp.all true in
#check @actual_memory_parser_derives_the_entire_low_word_from_every_input_byte_array
#print axioms actual_memory_parser_derives_the_entire_low_word_from_every_input_byte_array
end ShielddSecurity.TransferBlstParserValue01
