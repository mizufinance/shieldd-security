import ShielddSecurity.TransferBlstArmInverseCarrySplit01
import ShielddSecurity.TransferBlstArmInverseSignedWordMultiply01
import ShielddSecurity.TransferBlstArmInversePackedFactorWords01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseLowProduct01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseWordNegation01 (sourceNegatedWordsAndCarry)
open TransferBlstArmInverseSignedWordPrepare01 (sourceMaskPreparedWords)
open TransferBlstArmInverseWordMultiplyCarry01 (sourceUnsignedWordMultiply)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
open TransferBlstArmInverseFactorMagnitude01 (sourceFactorMagnitudeWord)
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode sourceSignedWordMeaning)
attribute [local irreducible] sourceNegatedWordsAndCarry sourceMaskPreparedWords
  sourceUnsignedWordMultiply sourceFactorSignMask sourceFactorMagnitudeWord sourceSignedWordCode

/-! Coefficient low-word multiplication needs modulo-width correctness even
for a negative factor times zero. Retain the source negation carry rather
than assume it is clear. These are source arithmetic lemmas; the split
coefficient routine's full layout and extra-word equation remain open. -/

theorem every_negated_word_block_has_the_exact_negative_entire_input_residue_including_zero
    (words : List UInt64) :
    (packWords (sourceNegatedWordsAndCarry words).1 : Int) % ((radix64 ^ words.length : Nat) : Int) =
      (-(packWords words : Int)) % ((radix64 ^ words.length : Nat) : Int) := by
  have conserved := TransferBlstArmInverseWordNegation01.original_complement_add_one_conserves_the_entire_word_value_and_last_arithmetic_carry words
  have cast := congrArg (fun value : Nat => (value : Int)) conserved
  dsimp only at cast
  simp only [Nat.cast_add, Nat.cast_mul] at cast
  have algebra : (packWords (sourceNegatedWordsAndCarry words).1 : Int) =
      -(packWords words : Int) + ((radix64 ^ words.length : Nat) : Int) *
        (1 - ((sourceNegatedWordsAndCarry words).2.toNat : Int)) := by
    rw [Int.mul_sub, Int.mul_one]
    omega
  rw [algebra, Int.add_mul_emod_self_left]

theorem every_coded_signed_factor_prepares_the_exact_signed_input_residue_including_zero
    (words : List UInt64) (factor : Int)
    (lower : -9223372036854775808 ≤ factor) (upper : factor < 9223372036854775808) :
    (packWords (sourceMaskPreparedWords words (sourceFactorSignMask (sourceSignedWordCode factor))).1 : Int) %
        ((radix64 ^ words.length : Nat) : Int) =
      (if factor < 0 then -(packWords words : Int) else (packWords words : Int)) %
        ((radix64 ^ words.length : Nat) : Int) := by
  rw [TransferBlstArmInverseSignedWordPrepare01.the_original_coded_factor_derives_its_entire_source_preparation_mask factor lower upper]
  by_cases negative : factor < 0
  · simp only [if_pos negative,
      TransferBlstArmInverseSignedWordPrepare01.the_original_all_ones_mask_preparation_is_exactly_the_qualified_word_negation]
    exact every_negated_word_block_has_the_exact_negative_entire_input_residue_including_zero words
  · simp only [if_neg negative,
      (TransferBlstArmInverseSignedWordPrepare01.the_original_zero_mask_preparation_has_clear_carry_and_the_entire_original_value words).2]

theorem every_sufficiently_long_word_vector_has_the_exact_prefix_residue_at_any_symbolic_boundary
    (words : List UInt64) (count : Nat) (enough : count ≤ words.length) :
    packWords (words.take count) = packWords words % radix64 ^ count := by
  have split := TransferBlstArmInverseCarrySplit01.the_entire_low_word_block_is_the_exact_full_value_residue_at_its_boundary
    (words.take count) (words.drop count)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left enough] at split
  exact split.symm

def sourceSignedLowProductWords (words : List UInt64) (factor : UInt64) : List UInt64 :=
  ((sourceUnsignedWordMultiply (sourceMaskPreparedWords words (sourceFactorSignMask factor)).1
    (sourceFactorMagnitudeWord factor)).1).take words.length

theorem every_source_low_word_product_retains_the_entire_original_input_width
    (words : List UInt64) (factor : UInt64) :
    (sourceSignedLowProductWords words factor).length = words.length := by
  have count := TransferBlstArmInverseWordMultiplyCarry01.original_unsigned_word_product_retains_one_extra_output_word
    (sourceMaskPreparedWords words (sourceFactorSignMask factor)).1 (sourceFactorMagnitudeWord factor)
  rw [TransferBlstArmInverseSignedWordPrepare01.every_source_mask_preparation_retains_the_entire_input_word_count] at count
  unfold sourceSignedLowProductWords
  rw [List.length_take, count, Nat.min_eq_left (Nat.le_succ _)]

theorem every_coded_source_low_word_product_has_the_entire_signed_product_residue_including_zero
    (words : List UInt64) (factor : Int)
    (lower : -9223372036854775808 ≤ factor) (upper : factor < 9223372036854775808) :
    (packWords (sourceSignedLowProductWords words (sourceSignedWordCode factor)) : Int) =
      ((packWords words : Int) * factor) % ((radix64 ^ words.length : Nat) : Int) := by
  let prepared := (sourceMaskPreparedWords words (sourceFactorSignMask (sourceSignedWordCode factor))).1
  let magnitude := sourceFactorMagnitudeWord (sourceSignedWordCode factor)
  have count := TransferBlstArmInverseWordMultiplyCarry01.original_unsigned_word_product_retains_one_extra_output_word prepared magnitude
  rw [TransferBlstArmInverseSignedWordPrepare01.every_source_mask_preparation_retains_the_entire_input_word_count] at count
  have leading := every_sufficiently_long_word_vector_has_the_exact_prefix_residue_at_any_symbolic_boundary
    (sourceUnsignedWordMultiply prepared magnitude).1 words.length (by omega)
  rw [(TransferBlstArmInverseWordMultiplyOverflow01.original_entire_unsigned_word_product_has_no_final_overflow_and_the_exact_full_value prepared magnitude).2] at leading
  have cast := congrArg (fun value : Nat => (value : Int)) leading
  dsimp only at cast
  rw [Int.natCast_emod, Nat.cast_mul] at cast
  have preparation := every_coded_signed_factor_prepares_the_exact_signed_input_residue_including_zero words factor lower upper
  have factorValue := TransferBlstArmInverseSignedWordMultiply01.every_coded_signed_factor_is_its_entire_word_magnitude_with_the_original_sign factor lower upper
  change (packWords (sourceSignedLowProductWords words (sourceSignedWordCode factor)) : Int) = _ at cast
  rw [cast, Int.mul_emod, preparation, ← Int.mul_emod]
  by_cases negative : factor < 0
  · rw [if_pos negative] at factorValue ⊢
    rw [factorValue]
    congr 1
    ring1
  · rw [if_neg negative] at factorValue ⊢
    rw [factorValue]

attribute [local irreducible] sourceSignedLowProductWords

theorem every_entire_source_factor_word_has_a_bounded_signed_integer_meaning
    (factor : UInt64) : -9223372036854775808 ≤ sourceSignedWordMeaning factor ∧
      sourceSignedWordMeaning factor < 9223372036854775808 := by
  have bounded : factor.toNat < 18446744073709551616 := factor.toNat_lt
  unfold sourceSignedWordMeaning
  split_ifs <;> omega

theorem every_source_factor_word_produces_the_entire_low_product_residue_of_its_actual_signed_meaning
    (words : List UInt64) (factor : UInt64) :
    (packWords (sourceSignedLowProductWords words factor) : Int) =
      ((packWords words : Int) * sourceSignedWordMeaning factor) % ((radix64 ^ words.length : Nat) : Int) := by
  have range := every_entire_source_factor_word_has_a_bounded_signed_integer_meaning factor
  have result := every_coded_source_low_word_product_has_the_entire_signed_product_residue_including_zero
    words (sourceSignedWordMeaning factor) range.1 range.2
  rw [TransferBlstArmInversePackedFactorWords01.every_entire_signed_word_decode_codes_back_to_the_original_word] at result
  exact result

set_option pp.all true in
#check @every_negated_word_block_has_the_exact_negative_entire_input_residue_including_zero
#print axioms every_negated_word_block_has_the_exact_negative_entire_input_residue_including_zero
set_option pp.all true in
#check @every_coded_signed_factor_prepares_the_exact_signed_input_residue_including_zero
#print axioms every_coded_signed_factor_prepares_the_exact_signed_input_residue_including_zero
set_option pp.all true in
#check @every_sufficiently_long_word_vector_has_the_exact_prefix_residue_at_any_symbolic_boundary
#print axioms every_sufficiently_long_word_vector_has_the_exact_prefix_residue_at_any_symbolic_boundary
set_option pp.all true in
#check @sourceSignedLowProductWords
#print axioms sourceSignedLowProductWords
set_option pp.all true in
#check @every_source_low_word_product_retains_the_entire_original_input_width
#print axioms every_source_low_word_product_retains_the_entire_original_input_width
set_option pp.all true in
#check @every_coded_source_low_word_product_has_the_entire_signed_product_residue_including_zero
#print axioms every_coded_source_low_word_product_has_the_entire_signed_product_residue_including_zero
set_option pp.all true in
#check @every_entire_source_factor_word_has_a_bounded_signed_integer_meaning
#print axioms every_entire_source_factor_word_has_a_bounded_signed_integer_meaning
set_option pp.all true in
#check @every_source_factor_word_produces_the_entire_low_product_residue_of_its_actual_signed_meaning
#print axioms every_source_factor_word_produces_the_entire_low_product_residue_of_its_actual_signed_meaning
end ShielddSecurity.TransferBlstArmInverseLowProduct01
