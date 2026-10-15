import ShielddSecurity.TransferBlstArmInverseWordAbsolute01
import ShielddSecurity.TransferBlstArmInverseSignedExtrQuotient01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseShiftAbsolute01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseExtrChain01 (sourceExtractChain)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
open TransferBlstArmInverseSignedProductDecode01 (sourceSignedRadixDecode)
open TransferBlstArmInverseSignedWordPrepare01 (sourceMaskPreparedWords)
attribute [local irreducible] sourceExtractChain sourceFactorSignMask sourceMaskPreparedWords

/-! Full source signed decoding, adjacent EXTR, unshifted-top ASR and
EOR/add-one correction compose to the quotient magnitude. The full quotient
range is explicit until instantiated from the original batch range theorem.
This remains a source arithmetic statement, not compiled native execution. -/

theorem the_entire_signed_radix_decoder_preserves_its_input_residue
    (half unsigned : Int) :
    sourceSignedRadixDecode half unsigned % (2 * half) = unsigned % (2 * half) := by
  by_cases sign : half ≤ unsigned
  · rw [sourceSignedRadixDecode, if_pos sign, Int.sub_emod_right]
  · rw [sourceSignedRadixDecode, if_neg sign]

theorem positive_integer_division_preserves_the_exact_negativity_test
    (value divisor : Int) (positive : 0 < divisor) : value / divisor < 0 ↔ value < 0 := by
  have nonnegative := Int.ediv_nonneg_iff_of_pos (a := value) positive
  omega

attribute [local irreducible] sourceSignedRadixDecode

theorem source_extr_top_asr_and_word_absolute_correction_derive_the_entire_quotient_magnitude
    (words : List UInt64) (count shift : Nat) (value : Int)
    (width : words.length = count + 1) (positive : 0 < shift) (bounded : shift < 64)
    (decoded : sourceSignedRadixDecode ((radix64 ^ count * 9223372036854775808 : Nat) : Int)
      (packWords words : Int) = value)
    (magnitudeSmall : (value / ((2 ^ shift : Nat) : Int)).natAbs < radix64 ^ count) :
    packWords (sourceMaskPreparedWords (sourceExtractChain shift words).1
      (sourceFactorSignMask (sourceExtractChain shift words).2)).1 =
        (value / ((2 ^ shift : Nat) : Int)).natAbs := by
  have outputWidth := TransferBlstArmInverseExtrChain01.every_original_adjacent_extraction_chain_retains_exactly_the_lower_word_count shift words
  rw [width, Nat.add_sub_cancel] at outputWidth
  have capacity : ((radix64 ^ (count + 1) : Nat) : Int) =
      2 * ((radix64 ^ count * 9223372036854775808 : Nat) : Int) := by
    have cast := congrArg (fun n : Nat => (n : Int))
      (TransferBlstArmInverseSignedProductDecode01.the_extra_output_word_capacity_is_exactly_twice_the_entire_signed_half_capacity count)
    dsimp only at cast
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using cast
  have residue := the_entire_signed_radix_decoder_preserves_its_input_residue
    ((radix64 ^ count * 9223372036854775808 : Nat) : Int) (packWords words : Int)
  rw [decoded, ←capacity] at residue
  have quotient := TransferBlstArmInverseSignedExtrQuotient01.the_entire_source_extraction_chain_derives_the_signed_integer_quotient_residue
    words count shift value width positive bounded residue.symm
  have reduced := congrArg (fun n : Int => n % ((radix64 ^ count : Nat) : Int)) quotient
  dsimp only at reduced
  rw [Int.emod_emod] at reduced
  have nonempty : words ≠ [] := by intro empty; rw [empty, List.length_nil] at width; omega
  have sign := TransferBlstArmInverseTopWordSign01.every_nonempty_source_word_input_derives_its_entire_retained_top_sign_mask
    shift words nonempty
  rw [width, Nat.add_sub_cancel, decoded] at sign
  have divisorPositive : (0 : Int) < ((2 ^ shift : Nat) : Int) := by exact_mod_cast (Nat.two_pow_pos shift)
  have quotientSign := positive_integer_division_preserves_the_exact_negativity_test value ((2 ^ shift : Nat) : Int) divisorPositive
  have maskOrigin : sourceFactorSignMask (sourceExtractChain shift words).2 =
      if value / ((2 ^ shift : Nat) : Int) < 0 then (-1 : UInt64) else 0 := by
    simpa only [quotientSign] using sign
  have absolute := TransferBlstArmInverseWordAbsolute01.exact_signed_quotient_words_and_sign_mask_derive_the_entire_natural_magnitude
    (sourceExtractChain shift words).1 (value / ((2 ^ shift : Nat) : Int))
    (sourceFactorSignMask (sourceExtractChain shift words).2)
    (by simpa only [outputWidth] using magnitudeSmall)
    (by simpa only [outputWidth] using reduced) maskOrigin
  exact absolute

set_option pp.all true in
#check @the_entire_signed_radix_decoder_preserves_its_input_residue
#print axioms the_entire_signed_radix_decoder_preserves_its_input_residue
set_option pp.all true in
#check @positive_integer_division_preserves_the_exact_negativity_test
#print axioms positive_integer_division_preserves_the_exact_negativity_test
set_option pp.all true in
#check @source_extr_top_asr_and_word_absolute_correction_derive_the_entire_quotient_magnitude
#print axioms source_extr_top_asr_and_word_absolute_correction_derive_the_entire_quotient_magnitude
end ShielddSecurity.TransferBlstArmInverseShiftAbsolute01
