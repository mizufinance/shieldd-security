import ShielddSecurity.TransferCommonwareMapBytes01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstEncoder01
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferSqrtProducerField01 (sourceFieldValue)
open TransferCommonwareMapBytes01
open TransferBoundedNativeCodec01 (nullifierModulus)

theorem source_be_encoder_read_index_is_inside_the_four_limb_buffer (index : Fin 32) :
    (31-index.val)/8 < 4 := by have := index.isLt; omega

/-- Exact64-bit limb path of locked BLST bytes.h be_bytes_from_limbs.
Pointer validity/alias/architecture and from_mont_256 semantics remain separate. -/
def sourceBEFromLimbs64 (words : Vector UInt64 4) (index : Fin 32) : UInt8 :=
  let n := 31-index.val
  UInt8.ofNat ((words[n/8]'(source_be_encoder_read_index_is_inside_the_four_limb_buffer index)) >>>
    UInt64.ofNat (8*(n%8))).toNat

theorem actual_blst_be_from_limbs_byte31_has_the_exact_low_word_remainder (words : Vector UInt64 4) :
    (sourceBEFromLimbs64 words ⟨31,by decide⟩).toNat = words[0].toNat % 256 := by
  simp only [sourceBEFromLimbs64,Nat.sub_self,Nat.zero_div,Nat.zero_mod,Nat.mul_zero,
    UInt64.toNat_shiftRight,UInt64.toNat_ofNat',Nat.zero_mod,Nat.shiftRight_eq_div_pow,
    pow_zero,Nat.div_one,UInt8.toNat_ofNat']

theorem actual_blst_be_from_limbs_byte31_and_one_has_the_packed_limb_parity (words : Vector UInt64 4) :
    (sourceBEFromLimbs64 words ⟨31,by decide⟩ &&& 1).toNat = packWords words.toList % 2 := by
  rw [UInt8.toNat_and,actual_blst_be_from_limbs_byte31_has_the_exact_low_word_remainder]
  change (words[0].toNat % 256) &&& 1 = _
  rw [Nat.and_one_is_mod,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 256)]
  have low := TransferScalarMontgomeryValue01.packed_vector_modulo_radix_is_actual_low_word
    words.toList
  have listHead : words.toList.headD 0 = words[0] := by simp [List.head?_eq_getElem?]
  rw [listHead] at low
  have parity := congrArg (fun n : Nat => n%2) low
  dsimp only at parity
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ radix64)] at parity
  exact parity.symm

/-- The remaining from_mont output/value contract is explicit. The C byte
loop itself derives parity; no desired byte, root or map output is a premise. -/
theorem actual_blst_encoder_low_bit_derives_field_parity_from_normalized_limb_value
    (words : Vector UInt64 4) (value : ZMod nullifierModulus)
    (normalizedValue : packWords words.toList = value.val) :
    (sourceBEFromLimbs64 words ⟨31,by decide⟩ &&& 1).toNat = value.val % 2 := by
  rw [actual_blst_be_from_limbs_byte31_and_one_has_the_packed_limb_parity,normalizedValue]

set_option pp.all true in
#check @source_be_encoder_read_index_is_inside_the_four_limb_buffer
#print axioms source_be_encoder_read_index_is_inside_the_four_limb_buffer
set_option pp.all true in
#check @sourceBEFromLimbs64
#print axioms sourceBEFromLimbs64
set_option pp.all true in
#check @actual_blst_be_from_limbs_byte31_has_the_exact_low_word_remainder
#print axioms actual_blst_be_from_limbs_byte31_has_the_exact_low_word_remainder
set_option pp.all true in
#check @actual_blst_be_from_limbs_byte31_and_one_has_the_packed_limb_parity
#print axioms actual_blst_be_from_limbs_byte31_and_one_has_the_packed_limb_parity
set_option pp.all true in
#check @actual_blst_encoder_low_bit_derives_field_parity_from_normalized_limb_value
#print axioms actual_blst_encoder_low_bit_derives_field_parity_from_normalized_limb_value
end ShielddSecurity.TransferBlstEncoder01
