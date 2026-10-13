import ShielddSecurity.TransferBlstEncoder01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstByteCaller01
open TransferBlstEncoder01
open TransferScalarWordPrimitives01 (packWords)
open TransferBoundedNativeCodec01 (nullifierModulus)

def sourceLEParseStep (word : UInt64) (byte : UInt8) : UInt64 :=
  (word <<< 8) ||| UInt64.ofNat byte.toNat

theorem actual_wrapped_parser_shift_or_step_derives_the_input_byte_parity
    (word : UInt64) (byte : UInt8) : (sourceLEParseStep word byte).toNat % 2 = byte.toNat % 2 := by
  have shiftZero : (word <<< (8 : UInt64)).toNat % 2 = 0 := by
    rw [UInt64.toNat_shiftLeft]
    change (word.toNat <<< 8 % 2^64) % 2 = 0
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2^64),Nat.shiftLeft_eq]
    simp [Nat.mul_mod]
  have byteBound : byte.toNat < 2^64 := Nat.lt_trans byte.toNat_lt (by decide : 2^8 < 2^64)
  unfold sourceLEParseStep
  rw [UInt64.toNat_or,UInt64.toNat_ofNat',Nat.mod_eq_of_lt byteBound]
  change ((word <<< (8 : UInt64)).toNat ||| byte.toNat) % 2^1 = byte.toNat % 2^1
  rw [Nat.or_mod_two_pow]
  change ((word <<< (8 : UInt64)).toNat % 2) ||| (byte.toNat % 2) = byte.toNat % 2
  rw [shiftZero,Nat.zero_or]

def sourceLEFromLimbs64 (words : Vector UInt64 4) (index : Fin 32) : UInt8 :=
  UInt8.ofNat ((words[index.val/8]'(by have := index.isLt; omega)) >>>
    UInt64.ofNat (8*(index.val%8))).toNat

def sourceScalarLEBytes64 (words : Vector UInt64 4) : Vector UInt8 32 :=
  Vector.ofFn (sourceLEFromLimbs64 words)

theorem actual_scalar_le_encoder_byte_zero_has_the_low_word_remainder (words : Vector UInt64 4) :
    (sourceScalarLEBytes64 words)[0].toNat = words[0].toNat % 256 := by
  simp only [sourceScalarLEBytes64,Vector.getElem_ofFn,sourceLEFromLimbs64,
    Nat.zero_div,Nat.zero_mod,Nat.mul_zero,UInt64.toNat_shiftRight,UInt64.toNat_ofNat',
    Nat.zero_mod,Nat.shiftRight_eq_div_pow,pow_zero,Nat.div_one,UInt8.toNat_ofNat']

def sourceLEParseMemoryStep (bytes : Vector UInt8 32)
    (state : UInt64 × Vector UInt64 4) (index : Fin 32) : UInt64 × Vector UInt64 4 :=
  let word := sourceLEParseStep state.1 bytes[index.val]
  (word,state.2.set (index.val/8) word (by have := index.isLt; omega))

def sourceLEParseMemory64 (bytes : Vector UInt8 32)
    (initialBuffer : Vector UInt64 4 := Vector.replicate 4 0) : Vector UInt64 4 :=
  ((List.finRange 32).reverse.foldl (sourceLEParseMemoryStep bytes)
    (0,initialBuffer)).2

attribute [local irreducible] sourceLEParseMemoryStep sourceLEParseStep

theorem actual_parser_store_at_index_zero_derives_parity_independent_of_prior_memory
    (bytes : Vector UInt8 32) (state : UInt64 × Vector UInt64 4) :
    (sourceLEParseMemoryStep bytes state ⟨0,by decide⟩).2[0].toNat % 2 = bytes[0].toNat % 2 := by
  simp only [sourceLEParseMemoryStep,Vector.getElem_set_self]
  exact actual_wrapped_parser_shift_or_step_derives_the_input_byte_parity _ _

theorem actual_memory_parser_final_store_derives_low_word_parity (bytes : Vector UInt8 32)
    (initialBuffer : Vector UInt64 4) :
    (sourceLEParseMemory64 bytes initialBuffer)[0].toNat % 2 = bytes[0].toNat % 2 := by
  unfold sourceLEParseMemory64
  rw [List.finRange_succ,List.reverse_cons,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil]
  exact actual_parser_store_at_index_zero_derives_parity_independent_of_prior_memory bytes _

def sourceScalarBendianBytes64 (words : Vector UInt64 4) (index : Fin 32) : UInt8 :=
  sourceBEFromLimbs64 (sourceLEParseMemory64 (sourceScalarLEBytes64 words)) index

theorem actual_scalar_le_parser_be_encoder_chain_derives_original_packed_parity
    (words : Vector UInt64 4) :
    (sourceScalarBendianBytes64 words ⟨31,by decide⟩ &&& 1).toNat = packWords words.toList % 2 := by
  rw [sourceScalarBendianBytes64,UInt8.toNat_and,
    actual_blst_be_from_limbs_byte31_has_the_exact_low_word_remainder]
  change ((sourceLEParseMemory64 (sourceScalarLEBytes64 words))[0].toNat % 256) &&& 1 = _
  rw [Nat.and_one_is_mod,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 256),
    actual_memory_parser_final_store_derives_low_word_parity,
    actual_scalar_le_encoder_byte_zero_has_the_low_word_remainder,
    Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 256)]
  have low := TransferScalarMontgomeryValue01.packed_vector_modulo_radix_is_actual_low_word words.toList
  have listHead : words.toList.headD 0 = words[0] := by simp [List.head?_eq_getElem?]
  rw [listHead] at low
  have parity := congrArg (fun n : Nat => n%2) low
  dsimp only at parity
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ TransferScalarSerializationRange01.radix64)] at parity
  exact parity.symm

theorem actual_commonware_scalar_encoder_chain_derives_field_parity_from_montgomery_normalization
    (words : Vector UInt64 4) (value : ZMod nullifierModulus)
    (normalization : packWords words.toList = value.val) :
    (sourceScalarBendianBytes64 words ⟨31,by decide⟩ &&& 1).toNat = value.val % 2 := by
  rw [actual_scalar_le_parser_be_encoder_chain_derives_original_packed_parity,normalization]
def sourceCommonwareEncodedRootGuard (choice : Bool) (words : Vector UInt64 4)
    (root : ZMod nullifierModulus) : ZMod nullifierModulus :=
  if ((sourceScalarBendianBytes64 words ⟨31,by decide⟩ &&& 1).toNat == 1) != choice
    then -root else root

theorem actual_commonware_encoded_root_guard_derives_the_qualified_field_normalization
    (choice : Bool) (words : Vector UInt64 4) (root : ZMod nullifierModulus)
    (normalization : packWords words.toList = root.val) :
    sourceCommonwareEncodedRootGuard choice words root =
      TransferCommonwareMapRoots01.normalizeRoot choice root := by
  unfold sourceCommonwareEncodedRootGuard
  rw [actual_commonware_scalar_encoder_chain_derives_field_parity_from_montgomery_normalization
    words root normalization]
  cases choice with
  | false =>
    by_cases low : root.val % 2 = 0
    · simp [TransferCommonwareMapRoots01.normalizeRoot,low]
    · have one : root.val % 2 = 1 := by omega
      simp [TransferCommonwareMapRoots01.normalizeRoot,one]
  | true =>
    by_cases one : root.val % 2 = 1 <;>
      simp [TransferCommonwareMapRoots01.normalizeRoot,one]
set_option pp.all true in
#check @sourceLEParseStep
#print axioms sourceLEParseStep
set_option pp.all true in
#check @actual_wrapped_parser_shift_or_step_derives_the_input_byte_parity
#print axioms actual_wrapped_parser_shift_or_step_derives_the_input_byte_parity
set_option pp.all true in
#check @sourceLEFromLimbs64
#print axioms sourceLEFromLimbs64
set_option pp.all true in
#check @sourceScalarLEBytes64
#print axioms sourceScalarLEBytes64
set_option pp.all true in
#check @actual_scalar_le_encoder_byte_zero_has_the_low_word_remainder
#print axioms actual_scalar_le_encoder_byte_zero_has_the_low_word_remainder
set_option pp.all true in
#check @sourceLEParseMemoryStep
#print axioms sourceLEParseMemoryStep
set_option pp.all true in
#check @sourceLEParseMemory64
#print axioms sourceLEParseMemory64
set_option pp.all true in
#check @actual_parser_store_at_index_zero_derives_parity_independent_of_prior_memory
#print axioms actual_parser_store_at_index_zero_derives_parity_independent_of_prior_memory
set_option pp.all true in
#check @actual_memory_parser_final_store_derives_low_word_parity
#print axioms actual_memory_parser_final_store_derives_low_word_parity
set_option pp.all true in
#check @sourceScalarBendianBytes64
#print axioms sourceScalarBendianBytes64
set_option pp.all true in
#check @actual_scalar_le_parser_be_encoder_chain_derives_original_packed_parity
#print axioms actual_scalar_le_parser_be_encoder_chain_derives_original_packed_parity
set_option pp.all true in
#check @actual_commonware_scalar_encoder_chain_derives_field_parity_from_montgomery_normalization
#print axioms actual_commonware_scalar_encoder_chain_derives_field_parity_from_montgomery_normalization
set_option pp.all true in
#check @sourceCommonwareEncodedRootGuard
#print axioms sourceCommonwareEncodedRootGuard
set_option pp.all true in
#check @actual_commonware_encoded_root_guard_derives_the_qualified_field_normalization
#print axioms actual_commonware_encoded_root_guard_derives_the_qualified_field_normalization
end ShielddSecurity.TransferBlstByteCaller01
