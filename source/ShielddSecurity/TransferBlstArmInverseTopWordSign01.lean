import ShielddSecurity.TransferBlstArmInverseExtrChain01
import ShielddSecurity.TransferBlstArmInverseSignedProductDecode01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseTopWordSign01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseExtrChain01 (sourceExtractChain)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
open TransferBlstArmInverseSignedProductDecode01 (sourceSignedRadixDecode)
attribute [local irreducible] sourceFactorSignMask

/-! The unshifted high word retained by EXTR supplies the sign of the whole
extra-word signed sum. ASR63 here is the source BitVec arithmetic shift;
native register origins and compiled instruction execution remain separate. -/

theorem every_source_extraction_chain_retains_the_original_unshifted_final_word
    (shift : Nat) (low : List UInt64) (top : UInt64) :
    (sourceExtractChain shift (low ++ [top])).2 = top := by
  induction low with
  | nil => rfl
  | cons head rest ih =>
    cases rest with
    | nil => rfl
    | cons next tail => exact ih

theorem a_bounded_low_part_derives_the_entire_unsigned_top_threshold
    (low capacity top half : Nat) (bounded : low < capacity) :
    capacity * half ≤ low + capacity * top ↔ half ≤ top := by
  constructor
  · intro above
    by_contra below
    have topSmall : top + 1 ≤ half := by omega
    have scaled := Nat.mul_le_mul_left capacity topSmall
    rw [Nat.mul_add, Nat.mul_one] at scaled
    omega
  · intro above
    have scaled := Nat.mul_le_mul_left capacity above
    omega

theorem an_unsigned_full_range_decodes_to_a_negative_integer_exactly_at_its_half_threshold
    (half unsigned : Int) (nonnegative : 0 ≤ unsigned) (bounded : unsigned < 2 * half) :
    sourceSignedRadixDecode half unsigned < 0 ↔ half ≤ unsigned := by
  by_cases sign : half ≤ unsigned
  · rw [sourceSignedRadixDecode, if_pos sign]
    omega
  · rw [sourceSignedRadixDecode, if_neg sign]
    omega

attribute [local irreducible] sourceExtractChain sourceSignedRadixDecode

theorem the_entire_appended_word_value_derives_the_exact_top_word_sign_threshold
    (low : List UInt64) (top : UInt64) :
    ((radix64 ^ low.length * 9223372036854775808 : Nat) : Int) ≤
      (packWords (low ++ [top]) : Int) ↔ 9223372036854775808 ≤ top.toNat := by
  have entire := TransferBlstArmInverseFirst01.symbolic_word_append_has_the_entire_radix_weighted_value low [top]
  have oneWord : packWords [top] = top.toNat := by simp only [packWords, Nat.mul_zero, Nat.add_zero]
  rw [oneWord] at entire
  have threshold := a_bounded_low_part_derives_the_entire_unsigned_top_threshold
    (packWords low) (radix64 ^ low.length) top.toNat 9223372036854775808
    (TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power low)
  rw [←entire] at threshold
  exact_mod_cast threshold

theorem original_retained_top_word_asr63_is_the_exact_sign_mask_of_the_entire_signed_input
    (shift : Nat) (low : List UInt64) (top : UInt64) :
    sourceFactorSignMask (sourceExtractChain shift (low ++ [top])).2 =
      if sourceSignedRadixDecode ((radix64 ^ low.length * 9223372036854775808 : Nat) : Int)
          (packWords (low ++ [top]) : Int) < 0 then (-1 : UInt64) else 0 := by
  have entireBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (low ++ [top])
  rw [List.length_append, List.length_singleton,
    TransferBlstArmInverseSignedProductDecode01.the_extra_output_word_capacity_is_exactly_twice_the_entire_signed_half_capacity] at entireBound
  have bounded : (packWords (low ++ [top]) : Int) <
      2 * ((radix64 ^ low.length * 9223372036854775808 : Nat) : Int) := by exact_mod_cast entireBound
  have sign := an_unsigned_full_range_decodes_to_a_negative_integer_exactly_at_its_half_threshold
    ((radix64 ^ low.length * 9223372036854775808 : Nat) : Int) (packWords (low ++ [top]) : Int)
    (Int.natCast_nonneg _) bounded
  have threshold := the_entire_appended_word_value_derives_the_exact_top_word_sign_threshold low top
  rw [every_source_extraction_chain_retains_the_original_unshifted_final_word,
    TransferBlstArmInverseSignMask01.original_factor_arithmetic_shift_mask_is_the_exact_word_constant]
  simp only [sign, threshold]

theorem every_nonempty_source_word_input_derives_its_entire_retained_top_sign_mask
    (shift : Nat) (words : List UInt64) (nonempty : words ≠ []) :
    sourceFactorSignMask (sourceExtractChain shift words).2 =
      if sourceSignedRadixDecode ((radix64 ^ (words.length - 1) * 9223372036854775808 : Nat) : Int)
          (packWords words : Int) < 0 then (-1 : UInt64) else 0 := by
  have split := List.dropLast_concat_getLast nonempty
  have sign := original_retained_top_word_asr63_is_the_exact_sign_mask_of_the_entire_signed_input
    shift words.dropLast (words.getLast nonempty)
  rw [split, List.length_dropLast] at sign
  exact sign

set_option pp.all true in
#check @every_source_extraction_chain_retains_the_original_unshifted_final_word
#print axioms every_source_extraction_chain_retains_the_original_unshifted_final_word
set_option pp.all true in
#check @a_bounded_low_part_derives_the_entire_unsigned_top_threshold
#print axioms a_bounded_low_part_derives_the_entire_unsigned_top_threshold
set_option pp.all true in
#check @an_unsigned_full_range_decodes_to_a_negative_integer_exactly_at_its_half_threshold
#print axioms an_unsigned_full_range_decodes_to_a_negative_integer_exactly_at_its_half_threshold
set_option pp.all true in
#check @the_entire_appended_word_value_derives_the_exact_top_word_sign_threshold
#print axioms the_entire_appended_word_value_derives_the_exact_top_word_sign_threshold
set_option pp.all true in
#check @original_retained_top_word_asr63_is_the_exact_sign_mask_of_the_entire_signed_input
#print axioms original_retained_top_word_asr63_is_the_exact_sign_mask_of_the_entire_signed_input
set_option pp.all true in
#check @every_nonempty_source_word_input_derives_its_entire_retained_top_sign_mask
#print axioms every_nonempty_source_word_input_derives_its_entire_retained_top_sign_mask
end ShielddSecurity.TransferBlstArmInverseTopWordSign01
