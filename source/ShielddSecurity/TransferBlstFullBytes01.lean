import ShielddSecurity.TransferBlstEncoder01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstFullBytes01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)

theorem symbolic_packed_word_quotient_is_the_actual_indexed_limb
    (words : List UInt64) (index : Nat) (inside : index < words.length) :
    packWords words / radix64^index % radix64 = words[index].toNat := by
  induction words generalizing index with
  | nil => simp only [List.length_nil] at inside; omega
  | cons word rest ih =>
    cases index with
    | zero =>
      simp only [Nat.pow_zero,Nat.div_one,List.getElem_cons_zero]
      exact TransferScalarMontgomeryValue01.packed_vector_modulo_radix_is_actual_low_word (word::rest)
    | succ index =>
      have wordBound : word.toNat < radix64 := word.toNat_lt
      have quotient : packWords (word::rest)/radix64 = packWords rest := by
        rw [packWords,Nat.add_mul_div_left _ _ (by decide : 0 < radix64),
          Nat.div_eq_of_lt wordBound,Nat.zero_add]
      rw [Nat.pow_succ',← Nat.div_div_eq_div_mul,quotient]
      exact ih index (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using inside)

theorem truncating_to_one_limb_retains_every_byte_inside_that_limb
    (value offset : Nat) (inside : offset < 8) :
    (value % radix64 / 256^offset) % 256 = (value / 256^offset) % 256 := by
  have split : radix64 = 256^offset*256^(8-offset) := by
    change 256^8 = _
    rw [← Nat.pow_add,show offset+(8-offset)=8 by omega]
  have remainderPositive : 1 ≤ 8-offset := by omega
  have divisor : 256 ∣ 256^(8-offset) := by
    have identity : 256^(8-offset) = 256*256^((8-offset)-1) := by
      rw [← Nat.pow_succ',show (8-offset-1).succ = 8-offset by omega]
    rw [identity]
    exact dvd_mul_right _ _
  rw [split,Nat.mod_mul_right_div_self,Nat.mod_mod_of_dvd _ divisor]

theorem symbolic_index_partition_is_the_exact_byte_denominator (index : Nat) :
    radix64^(index/8)*256^(index%8) = 256^index := by
  change (256^8)^(index/8)*256^(index%8) = _
  rw [← Nat.pow_mul,← Nat.pow_add,Nat.div_add_mod]

theorem actual_be_encoder_byte_is_the_actual_limb_byte_quotient
    (words : Vector UInt64 4) (index : Fin 32) :
    (TransferBlstEncoder01.sourceBEFromLimbs64 words index).toNat =
      (words[(31-index.val)/8]'(TransferBlstEncoder01.source_be_encoder_read_index_is_inside_the_four_limb_buffer index)).toNat
        /256^((31-index.val)%8) % 256 := by
  have offsetInside : (31-index.val)%8 < 8 := Nat.mod_lt _ (by decide)
  have amountInside : 8*((31-index.val)%8) < 64 := by omega
  simp only [TransferBlstEncoder01.sourceBEFromLimbs64,UInt8.toNat_ofNat',
    UInt64.toNat_shiftRight,UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (Nat.lt_trans amountInside (by decide : 64 < 2^64)),
    Nat.mod_eq_of_lt amountInside,Nat.shiftRight_eq_div_pow,Nat.pow_mul]

theorem actual_be_encoder_every_byte_is_the_original_packed_integer_byte
    (words : Vector UInt64 4) (index : Fin 32) :
    (TransferBlstEncoder01.sourceBEFromLimbs64 words index).toNat =
      packWords words.toList /256^(31-index.val) % 256 := by
  rw [actual_be_encoder_byte_is_the_actual_limb_byte_quotient]
  have limb := symbolic_packed_word_quotient_is_the_actual_indexed_limb
    words.toList ((31-index.val)/8)
    (by simpa only [Vector.length_toList] using
      TransferBlstEncoder01.source_be_encoder_read_index_is_inside_the_four_limb_buffer index)
  simp only [Vector.getElem_toList] at limb
  rw [← limb,truncating_to_one_limb_retains_every_byte_inside_that_limb
    _ _ (Nat.mod_lt _ (by decide)),Nat.div_div_eq_div_mul,
    symbolic_index_partition_is_the_exact_byte_denominator]

theorem actual_be_encoder_every_byte_derives_canonical_field_byte_from_normalized_value
    (words : Vector UInt64 4) (value : ZMod TransferBoundedNativeCodec01.nullifierModulus)
    (normalization : packWords words.toList = value.val) (index : Fin 32) :
    TransferBlstEncoder01.sourceBEFromLimbs64 words index =
      TransferCommonwareMapBytes01.canonicalBEByte value index := by
  apply UInt8.toNat_inj.mp
  rw [actual_be_encoder_every_byte_is_the_original_packed_integer_byte,normalization]
  simp only [TransferCommonwareMapBytes01.canonicalBEByte,UInt8.toNat_ofNat']
  exact (Nat.mod_mod _ _).symm
set_option pp.all true in
#check @symbolic_packed_word_quotient_is_the_actual_indexed_limb
#print axioms symbolic_packed_word_quotient_is_the_actual_indexed_limb
set_option pp.all true in
#check @truncating_to_one_limb_retains_every_byte_inside_that_limb
#print axioms truncating_to_one_limb_retains_every_byte_inside_that_limb
set_option pp.all true in
#check @symbolic_index_partition_is_the_exact_byte_denominator
#print axioms symbolic_index_partition_is_the_exact_byte_denominator
set_option pp.all true in
#check @actual_be_encoder_byte_is_the_actual_limb_byte_quotient
#print axioms actual_be_encoder_byte_is_the_actual_limb_byte_quotient
set_option pp.all true in
#check @actual_be_encoder_every_byte_is_the_original_packed_integer_byte
#print axioms actual_be_encoder_every_byte_is_the_original_packed_integer_byte
set_option pp.all true in
#check @actual_be_encoder_every_byte_derives_canonical_field_byte_from_normalized_value
#print axioms actual_be_encoder_every_byte_derives_canonical_field_byte_from_normalized_value
end ShielddSecurity.TransferBlstFullBytes01
