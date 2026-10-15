import ShielddSecurity.TransferBlstArmInverseLowProduct01
import ShielddSecurity.TransferBlstArmInverseFactorSignCorrection01
import ShielddSecurity.TransferBlstArmInverseSignedProductDecode01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSignedHighProduct01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseWordMultiply01 (sourceMultiplyWordHigh)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode sourceSignedWordMeaning)
attribute [local irreducible] sourceMultiplyWordHigh sourceFactorSignMask sourceSignedWordMeaning sourceSignedWordCode

/-! Signed-input times unsigned-factor high-word arithmetic. UMULH minus
the factor masked by the input sign yields the exact signed quotient code.
This supplies the high-limb arithmetic needed when the final coefficient
factor magnitude is below the signed-word half radix. Compiled SMULH and
the actual operand origins remain separate obligations. -/

theorem the_standard_integer_word_conversion_of_every_natural_is_its_entire_natural_word_code
    (value : Nat) : UInt64.ofInt (value : Int) = UInt64.ofNat value := by
  unfold UInt64.ofInt
  change UInt64.ofNat (((value : Int) % (UInt64.size : Int)).toNat) = UInt64.ofNat value
  rw [← Int.natCast_emod, Int.toNat_natCast, UInt64.ofNat_mod_size]

theorem the_source_unsigned_high_product_is_the_entire_integer_quotient_word_code
    (word multiplier : UInt64) :
    sourceMultiplyWordHigh word multiplier =
      UInt64.ofInt (((word.toNat : Int) * (multiplier.toNat : Int)) / (radix64 : Int)) := by
  rw [← Nat.cast_mul, ← Int.natCast_ediv,
    the_standard_integer_word_conversion_of_every_natural_is_its_entire_natural_word_code]
  unfold sourceMultiplyWordHigh
  rfl

def sourceSignedUnsignedHighWord (word multiplier : UInt64) : UInt64 :=
  sourceMultiplyWordHigh word multiplier - (multiplier &&& sourceFactorSignMask word)

theorem the_source_unsigned_high_product_and_input_sign_correction_derive_the_entire_signed_quotient_code
    (word multiplier : UInt64) :
    sourceSignedUnsignedHighWord word multiplier =
      UInt64.ofInt ((sourceSignedWordMeaning word * (multiplier.toNat : Int)) / (radix64 : Int)) := by
  by_cases negative : 9223372036854775808 ≤ word.toNat
  · simp only [sourceSignedUnsignedHighWord,
      TransferBlstArmInverseSignMask01.original_factor_arithmetic_shift_mask_is_the_exact_word_constant,
      if_pos negative, UInt64.and_neg_one, sourceSignedWordMeaning]
    have algebra : ((word.toNat : Int) - 18446744073709551616) * (multiplier.toNat : Int) =
        (word.toNat : Int) * (multiplier.toNat : Int) + (radix64 : Int) * (-(multiplier.toNat : Int)) := by
      change ((word.toNat : Int) - 18446744073709551616) * (multiplier.toNat : Int) =
        (word.toNat : Int) * (multiplier.toNat : Int) + 18446744073709551616 * (-(multiplier.toNat : Int))
      ring1
    rw [algebra, Int.add_mul_ediv_left _ _ (by decide : (radix64 : Int) ≠ 0),
      UInt64.ofInt_add, UInt64.ofInt_neg,
      the_standard_integer_word_conversion_of_every_natural_is_its_entire_natural_word_code,
      UInt64.ofNat_toNat, ← the_source_unsigned_high_product_is_the_entire_integer_quotient_word_code,
      UInt64.sub_eq_add_neg]
  · simp only [sourceSignedUnsignedHighWord,
      TransferBlstArmInverseSignMask01.original_factor_arithmetic_shift_mask_is_the_exact_word_constant,
      if_neg negative, UInt64.and_zero, UInt64.sub_zero, sourceSignedWordMeaning]
    exact the_source_unsigned_high_product_is_the_entire_integer_quotient_word_code word multiplier

attribute [local irreducible] sourceSignedUnsignedHighWord

theorem every_signed_word_times_unsigned_word_quotient_fits_the_entire_signed_word_range
    (word multiplier : UInt64) :
    -9223372036854775808 ≤ (sourceSignedWordMeaning word * (multiplier.toNat : Int)) / (radix64 : Int) ∧
      (sourceSignedWordMeaning word * (multiplier.toNat : Int)) / (radix64 : Int) < 9223372036854775808 := by
  have range := TransferBlstArmInverseLowProduct01.every_entire_source_factor_word_has_a_bounded_signed_integer_meaning word
  have absolute := TransferBlstArmInverseSignedProductDecode01.every_unsigned_word_input_times_signed64_factor_fits_strictly_inside_the_full_signed_output_range
    [multiplier] (sourceSignedWordMeaning word) range.1 range.2
  simp only [packWords, Nat.mul_zero, Nat.add_zero, List.length_singleton, Nat.pow_one] at absolute
  rw [Int.mul_comm] at absolute
  have castBound : (((sourceSignedWordMeaning word * (multiplier.toNat : Int)).natAbs : Nat) : Int) <
      (18446744073709551616 : Int) * 9223372036854775808 := by exact_mod_cast absolute
  have upper := Int.le_natAbs (a := sourceSignedWordMeaning word * (multiplier.toNat : Int))
  have lower := Int.le_natAbs (a := -(sourceSignedWordMeaning word * (multiplier.toNat : Int)))
  rw [Int.natAbs_neg] at lower
  change -9223372036854775808 ≤ (sourceSignedWordMeaning word * (multiplier.toNat : Int)) / 18446744073709551616 ∧
    (sourceSignedWordMeaning word * (multiplier.toNat : Int)) / 18446744073709551616 < 9223372036854775808
  omega

theorem the_source_corrected_high_product_decodes_to_the_entire_signed_integer_quotient
    (word multiplier : UInt64) :
    sourceSignedWordMeaning (sourceSignedUnsignedHighWord word multiplier) =
      (sourceSignedWordMeaning word * (multiplier.toNat : Int)) / (radix64 : Int) := by
  have range := every_signed_word_times_unsigned_word_quotient_fits_the_entire_signed_word_range word multiplier
  have decoded := TransferBlstArmInverseSignedWord01.original_signed64_code_and_threshold_decode_recover_the_entire_factor_value
    ((sourceSignedWordMeaning word * (multiplier.toNat : Int)) / (radix64 : Int)) range.1 range.2
  rw [TransferBlstArmInverseFactorSignCorrection01.the_source_signed_word_code_is_the_entire_standard_integer_word_conversion] at decoded
  rw [the_source_unsigned_high_product_and_input_sign_correction_derive_the_entire_signed_quotient_code]
  exact decoded

set_option pp.all true in
#check @the_standard_integer_word_conversion_of_every_natural_is_its_entire_natural_word_code
#print axioms the_standard_integer_word_conversion_of_every_natural_is_its_entire_natural_word_code
set_option pp.all true in
#check @the_source_unsigned_high_product_is_the_entire_integer_quotient_word_code
#print axioms the_source_unsigned_high_product_is_the_entire_integer_quotient_word_code
set_option pp.all true in
#check @sourceSignedUnsignedHighWord
#print axioms sourceSignedUnsignedHighWord
set_option pp.all true in
#check @the_source_unsigned_high_product_and_input_sign_correction_derive_the_entire_signed_quotient_code
#print axioms the_source_unsigned_high_product_and_input_sign_correction_derive_the_entire_signed_quotient_code
set_option pp.all true in
#check @every_signed_word_times_unsigned_word_quotient_fits_the_entire_signed_word_range
#print axioms every_signed_word_times_unsigned_word_quotient_fits_the_entire_signed_word_range
set_option pp.all true in
#check @the_source_corrected_high_product_decodes_to_the_entire_signed_integer_quotient
#print axioms the_source_corrected_high_product_decodes_to_the_entire_signed_integer_quotient
end ShielddSecurity.TransferBlstArmInverseSignedHighProduct01
