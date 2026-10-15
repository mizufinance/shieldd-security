import ShielddSecurity.TransferBlstArmInverseExtrWord01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordParityMask01

/-! Source signed extraction of bit zero, expressed as one-bit extraction
and sign extension to UInt64. The resulting mask derives the AND operand
and unsigned no-borrow condition used by source loop control. Compiled SBFX,
PSTATE flags and instruction execution remain separate obligations. -/

def sourceParityWordMask (word : UInt64) : UInt64 :=
  UInt64.ofBitVec ((word.toBitVec.extractLsb' 0 1).signExtend 64)

theorem the_original_low_bit_extraction_has_the_exact_entire_unsigned_parity
    (word : UInt64) : (word.toBitVec.extractLsb' 0 1).toNat = word.toNat % 2 := by
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, UInt64.toNat_toBitVec]

theorem original_one_bit_signed_extraction_derives_the_exact_zero_or_all_ones_parity_mask
    (word : UInt64) : sourceParityWordMask word = if word.toNat % 2 = 1 then (-1 : UInt64) else 0 := by
  let bit := word.toBitVec.extractLsb' 0 1
  have low : bit.toNat = word.toNat % 2 := the_original_low_bit_extraction_has_the_exact_entire_unsigned_parity word
  have bounded := Nat.mod_lt word.toNat (by decide : 0 < 2)
  apply UInt64.toNat_inj.mp
  rw [sourceParityWordMask, UInt64.toNat_ofBitVec, BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  change bit.toNat % 2 ^ 64 + (if bit.msb then 2 ^ 64 - 2 ^ 1 else 0) =
    (if word.toNat % 2 = 1 then (-1 : UInt64) else 0).toNat
  by_cases odd : word.toNat % 2 = 1
  · have one : bit.toNat = 1 := low.trans odd
    have msb : bit.msb = true := by rw [BitVec.msb_eq_decide, one]; decide
    simp only [one, msb, if_pos odd]
    decide
  · have zero : bit.toNat = 0 := by omega
    have msb : bit.msb = false := by rw [BitVec.msb_eq_decide, zero]; decide
    simp only [zero, msb, if_neg odd]
    decide

attribute [local irreducible] sourceParityWordMask

theorem original_parity_mask_and_retains_the_entire_second_word_exactly_for_an_odd_first_word
    (first second : UInt64) : second &&& sourceParityWordMask first =
      if first.toNat % 2 = 1 then second else 0 := by
  simp only [original_one_bit_signed_extraction_derives_the_exact_zero_or_all_ones_parity_mask]
  by_cases odd : first.toNat % 2 = 1
  · simp only [if_pos odd, UInt64.and_neg_one]
  · simp only [if_neg odd, UInt64.and_zero]

theorem original_masked_subtraction_no_borrow_condition_is_exactly_even_first_or_ordered_odd_inputs
    (first second : UInt64) :
    (second &&& sourceParityWordMask first).toNat ≤ first.toNat ↔
      first.toNat % 2 = 0 ∨ second.toNat ≤ first.toNat := by
  rw [original_parity_mask_and_retains_the_entire_second_word_exactly_for_an_odd_first_word]
  have bounded := Nat.mod_lt first.toNat (by decide : 0 < 2)
  by_cases odd : first.toNat % 2 = 1
  · rw [if_pos odd]
    omega
  · rw [if_neg odd, UInt64.toNat_zero]
    omega

set_option pp.all true in
#check @sourceParityWordMask
#print axioms sourceParityWordMask
set_option pp.all true in
#check @the_original_low_bit_extraction_has_the_exact_entire_unsigned_parity
#print axioms the_original_low_bit_extraction_has_the_exact_entire_unsigned_parity
set_option pp.all true in
#check @original_one_bit_signed_extraction_derives_the_exact_zero_or_all_ones_parity_mask
#print axioms original_one_bit_signed_extraction_derives_the_exact_zero_or_all_ones_parity_mask
set_option pp.all true in
#check @original_parity_mask_and_retains_the_entire_second_word_exactly_for_an_odd_first_word
#print axioms original_parity_mask_and_retains_the_entire_second_word_exactly_for_an_odd_first_word
set_option pp.all true in
#check @original_masked_subtraction_no_borrow_condition_is_exactly_even_first_or_ordered_odd_inputs
#print axioms original_masked_subtraction_no_borrow_condition_is_exactly_even_first_or_ordered_odd_inputs
end ShielddSecurity.TransferBlstArmInverseWordParityMask01
