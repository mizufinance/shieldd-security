import ShielddSecurity.TransferBlstArmInverseSignMask01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseFactorMagnitude01
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode sourceSignedWordMeaning)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)

/-! Word arithmetic for the locked ASR/EOR/SUB factor magnitude sequence.
This models the entire word result, including the signed64 minimum value.
Instruction execution and provenance of the original factor remain open. -/

def sourceFactorMagnitudeWord (word : UInt64) : UInt64 :=
  (word ^^^ sourceFactorSignMask word) - sourceFactorSignMask word

theorem original_factor_xor_and_subtract_is_exact_unsigned_magnitude (word : UInt64) :
    (sourceFactorMagnitudeWord word).toNat =
      if 9223372036854775808 <= word.toNat then 18446744073709551616-word.toNat else word.toNat := by
  simp only [sourceFactorMagnitudeWord,
    TransferBlstArmInverseSignMask01.original_factor_arithmetic_shift_mask_is_the_exact_word_constant]
  have radix : (2:Nat)^64=18446744073709551616 := by decide +kernel
  have ones : (-1:UInt64).toNat=18446744073709551615 := by decide
  have size : UInt64.size=18446744073709551616 := by rfl
  have range := word.toNat_lt
  change word.toNat < 18446744073709551616 at range
  by_cases negative : 9223372036854775808 <= word.toNat
  · simp only [if_pos negative, UInt64.xor_neg_one, UInt64.toNat_sub, UInt64.toNat_not, ones, radix, size]
    omega
  · simp only [if_neg negative, UInt64.xor_zero, UInt64.toNat_sub, UInt64.toNat_zero, radix]
    omega

theorem original_factor_magnitude_word_is_the_entire_signed_word_absolute_value (word : UInt64) :
    (sourceFactorMagnitudeWord word).toNat = (sourceSignedWordMeaning word).natAbs := by
  have magnitude := original_factor_xor_and_subtract_is_exact_unsigned_magnitude word
  have range := word.toNat_lt
  change word.toNat < 18446744073709551616 at range
  by_cases negative : 9223372036854775808 <= word.toNat
  · rw [if_pos negative] at magnitude
    have sign : sourceSignedWordMeaning word <= 0 := by
      rw [sourceSignedWordMeaning, if_pos negative]
      omega
    have abs := Int.eq_neg_natAbs_of_nonpos sign
    rw [sourceSignedWordMeaning, if_pos negative] at abs
    rw [sourceSignedWordMeaning, if_pos negative]
    omega
  · rw [if_neg negative] at magnitude
    have sign : 0 <= sourceSignedWordMeaning word := by
      rw [sourceSignedWordMeaning, if_neg negative]
      omega
    have abs := Int.natAbs_of_nonneg sign
    rw [sourceSignedWordMeaning, if_neg negative] at abs
    rw [sourceSignedWordMeaning, if_neg negative]
    omega

theorem original_coded_signed_factor_asr_xor_subtract_recovers_integer_magnitude
    (value : Int) (lower : -9223372036854775808 <= value) (upper : value < 9223372036854775808) :
    (sourceFactorMagnitudeWord (sourceSignedWordCode value)).toNat=value.natAbs := by
  rw [original_factor_magnitude_word_is_the_entire_signed_word_absolute_value,
    TransferBlstArmInverseSignedWord01.original_signed64_code_and_threshold_decode_recover_the_entire_factor_value value lower upper]

set_option pp.all true in
#check @sourceFactorMagnitudeWord
#print axioms sourceFactorMagnitudeWord
set_option pp.all true in
#check @original_factor_xor_and_subtract_is_exact_unsigned_magnitude
#print axioms original_factor_xor_and_subtract_is_exact_unsigned_magnitude
set_option pp.all true in
#check @original_factor_magnitude_word_is_the_entire_signed_word_absolute_value
#print axioms original_factor_magnitude_word_is_the_entire_signed_word_absolute_value
set_option pp.all true in
#check @original_coded_signed_factor_asr_xor_subtract_recovers_integer_magnitude
#print axioms original_coded_signed_factor_asr_xor_subtract_recovers_integer_magnitude
end ShielddSecurity.TransferBlstArmInverseFactorMagnitude01
