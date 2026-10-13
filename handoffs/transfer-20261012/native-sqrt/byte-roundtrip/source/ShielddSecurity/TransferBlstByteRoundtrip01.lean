import ShielddSecurity.TransferBlstParserSchedule01
import ShielddSecurity.TransferBlstFullBytes01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstByteRoundtrip01
open TransferBlstByteCaller01
open TransferBlstFullBytes01
open TransferBlstParserSchedule01
open TransferScalarLittleEndianBytes01 (encodeLE decodeLE)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)

theorem actual_le_and_be_limb_writers_have_the_exact_reverse_index_correspondence
    (words : Vector UInt64 4) (index : Fin 32) :
    (sourceScalarLEBytes64 words)[index.val] =
      TransferBlstEncoder01.sourceBEFromLimbs64 words ⟨31-index.val,by have := index.isLt; omega⟩ := by
  have reverseIndex : 31-(31-index.val) = index.val := by have := index.isLt; omega
  simp only [sourceScalarLEBytes64,Vector.getElem_ofFn,sourceLEFromLimbs64,
    TransferBlstEncoder01.sourceBEFromLimbs64,reverseIndex]

theorem actual_le_limb_writer_every_byte_is_the_packed_integer_byte
    (words : Vector UInt64 4) (index : Fin 32) :
    ((sourceScalarLEBytes64 words)[index.val]).toNat = packWords words.toList /256^index.val % 256 := by
  rw [actual_le_and_be_limb_writers_have_the_exact_reverse_index_correspondence,
    actual_be_encoder_every_byte_is_the_original_packed_integer_byte,
    show 31-(31-index.val)=index.val by have := index.isLt; omega]

theorem symbolic_integer_le_encoder_index_is_the_exact_byte_quotient
    (width value index : Nat) (inside : index < width) :
    (encodeLE width value)[index]'(by rw [TransferScalarLittleEndianBytes01.typed_little_endian_encoding_has_exact_width]; exact inside) =
      UInt8.ofNat (value/256^index % 256) := by
  induction width generalizing value index with
  | zero => omega
  | succ width ih =>
    cases index with
    | zero => simp only [encodeLE,List.getElem_cons_zero,Nat.pow_zero,Nat.div_one]
    | succ index =>
      have indexBound : index < (encodeLE width (value/256)).length := by
        rw [TransferScalarLittleEndianBytes01.typed_little_endian_encoding_has_exact_width]
        omega
      change (encodeLE width (value/256))[index]'indexBound = _
      rw [ih _ _ (by omega),Nat.div_div_eq_div_mul,← Nat.pow_succ']

theorem actual_le_limb_writer_is_the_qualified_whole_integer_le_encoding
    (words : Vector UInt64 4) :
    (sourceScalarLEBytes64 words).toList = encodeLE 32 (packWords words.toList) := by
  apply List.ext_getElem
  · simp only [Vector.length_toList,TransferScalarLittleEndianBytes01.typed_little_endian_encoding_has_exact_width]
  · intro index leftBound rightBound
    have inside : index < 32 := by simpa only [Vector.length_toList] using leftBound
    rw [Vector.getElem_toList,symbolic_integer_le_encoder_index_is_the_exact_byte_quotient _ _ _ inside]
    apply UInt8.toNat_inj.mp
    rw [actual_le_limb_writer_every_byte_is_the_packed_integer_byte words ⟨index,inside⟩,
      UInt8.toNat_ofNat']
    exact (Nat.mod_mod _ _).symm

theorem symbolic_drop_of_le_integer_encoding_is_the_shifted_integer_encoding
    (width value skip : Nat) (inside : skip ≤ width) :
    (encodeLE width value).drop skip = encodeLE (width-skip) (value/256^skip) := by
  induction skip generalizing width value with
  | zero => simp only [List.drop_zero,Nat.sub_zero,Nat.pow_zero,Nat.div_one]
  | succ skip ih =>
    cases width with
    | zero => omega
    | succ width =>
      change (encodeLE width (value/256)).drop skip = _
      rw [ih _ _ (by omega),Nat.div_div_eq_div_mul,← Nat.pow_succ']
      have count : width-skip = (width+1)-(skip+1) := by omega
      rw [count]

theorem encoded_suffix_reconstructs_the_exact_shifted_bounded_integer
    (width value skip : Nat) (inside : skip ≤ width) (bounded : value < 256^width) :
    decodeLE ((encodeLE width value).drop skip) = value/256^skip := by
  rw [symbolic_drop_of_le_integer_encoding_is_the_shifted_integer_encoding _ _ _ inside]
  apply TransferScalarLittleEndianBytes01.typed_little_endian_encoding_reconstructs_bounded_integer
  apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 256))).mpr
  rw [← Nat.pow_add,show width-skip+skip=width by omega]
  exact bounded

theorem actual_memory_parser_of_the_actual_limb_le_bytes_recovers_every_limb
    (words : Vector UInt64 4) (initialBuffer : Vector UInt64 4) (limb : Fin 4) :
    (sourceLEParseMemory64 (sourceScalarLEBytes64 words) initialBuffer)[limb.val] = words[limb.val] := by
  apply UInt64.toNat_inj.mp
  rw [actual_parser_every_limb_is_the_reconstructed_byte_suffix,
    actual_le_limb_writer_is_the_qualified_whole_integer_le_encoding]
  have offset : 8*limb.val ≤ 32 := by have := limb.isLt; omega
  have bounded : packWords words.toList < 256^32 := by
    simpa only [Vector.length_toList] using
      TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power words.toList
  rw [encoded_suffix_reconstructs_the_exact_shifted_bounded_integer _ _ _ offset bounded]
  have denominator : 256^(8*limb.val) = radix64^limb.val := by rw [Nat.pow_mul]; rfl
  rw [denominator]
  have recovered := symbolic_packed_word_quotient_is_the_actual_indexed_limb
    words.toList limb.val (by simpa only [Vector.length_toList] using limb.isLt)
  simpa only [Vector.getElem_toList] using recovered

theorem actual_le_writer_parser_roundtrip_is_the_original_four_limb_vector
    (words : Vector UInt64 4) (initialBuffer : Vector UInt64 4) :
    sourceLEParseMemory64 (sourceScalarLEBytes64 words) initialBuffer = words := by
  apply Vector.ext
  intro index inside
  exact actual_memory_parser_of_the_actual_limb_le_bytes_recovers_every_limb words initialBuffer ⟨index,inside⟩

theorem actual_le_parser_be_writer_chain_derives_every_canonical_field_byte
    (words : Vector UInt64 4) (value : ZMod TransferBoundedNativeCodec01.nullifierModulus)
    (normalization : packWords words.toList = value.val) (index : Fin 32) :
    sourceScalarBendianBytes64 words index = TransferCommonwareMapBytes01.canonicalBEByte value index := by
  rw [sourceScalarBendianBytes64,actual_le_writer_parser_roundtrip_is_the_original_four_limb_vector]
  exact actual_be_encoder_every_byte_derives_canonical_field_byte_from_normalized_value words value normalization index
set_option pp.all true in
#check @actual_le_and_be_limb_writers_have_the_exact_reverse_index_correspondence
#print axioms actual_le_and_be_limb_writers_have_the_exact_reverse_index_correspondence
set_option pp.all true in
#check @actual_le_limb_writer_every_byte_is_the_packed_integer_byte
#print axioms actual_le_limb_writer_every_byte_is_the_packed_integer_byte
set_option pp.all true in
#check @symbolic_integer_le_encoder_index_is_the_exact_byte_quotient
#print axioms symbolic_integer_le_encoder_index_is_the_exact_byte_quotient
set_option pp.all true in
#check @actual_le_limb_writer_is_the_qualified_whole_integer_le_encoding
#print axioms actual_le_limb_writer_is_the_qualified_whole_integer_le_encoding
set_option pp.all true in
#check @symbolic_drop_of_le_integer_encoding_is_the_shifted_integer_encoding
#print axioms symbolic_drop_of_le_integer_encoding_is_the_shifted_integer_encoding
set_option pp.all true in
#check @encoded_suffix_reconstructs_the_exact_shifted_bounded_integer
#print axioms encoded_suffix_reconstructs_the_exact_shifted_bounded_integer
set_option pp.all true in
#check @actual_memory_parser_of_the_actual_limb_le_bytes_recovers_every_limb
#print axioms actual_memory_parser_of_the_actual_limb_le_bytes_recovers_every_limb
set_option pp.all true in
#check @actual_le_writer_parser_roundtrip_is_the_original_four_limb_vector
#print axioms actual_le_writer_parser_roundtrip_is_the_original_four_limb_vector
set_option pp.all true in
#check @actual_le_parser_be_writer_chain_derives_every_canonical_field_byte
#print axioms actual_le_parser_be_writer_chain_derives_every_canonical_field_byte
end ShielddSecurity.TransferBlstByteRoundtrip01
