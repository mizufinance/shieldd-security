import ShielddSecurity.TransferBlstArmInverseSignBit01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSignMask01
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode)

/-! Source word semantics of ASR by 63 in the locked factor normalization.
The arithmetic right shift is BitVec.sshiftRight, with the unsigned word
conversion explicit. Compiled instruction execution remains a separate claim. -/

def sourceFactorSignMask (word : UInt64) : UInt64 :=
  UInt64.ofBitVec (word.toBitVec.sshiftRight 63)

theorem original_factor_arithmetic_shift_by_63_is_the_exact_zero_or_all_ones_mask
    (word : UInt64) :
    (sourceFactorSignMask word).toNat =
      if 9223372036854775808 <= word.toNat then 18446744073709551615 else 0 := by
  rw [sourceFactorSignMask, UInt64.toNat_ofBitVec]
  have radix : (2:Nat)^64=18446744073709551616 := by decide +kernel
  have half : (2:Nat)^63=9223372036854775808 := by decide +kernel
  have msb : word.toBitVec.msb = decide (9223372036854775808 <= word.toNat) := by
    simpa only [UInt64.toNat_toBitVec] using (BitVec.msb_eq_decide word.toBitVec)
  have range := word.toNat_lt
  change word.toNat < 18446744073709551616 at range
  by_cases negative : 9223372036854775808 <= word.toNat
  · have sign : word.toBitVec.msb=true := by rw [msb]; exact decide_eq_true negative
    rw [BitVec.toNat_sshiftRight_of_msb_true sign, UInt64.toNat_toBitVec, Nat.shiftRight_eq_div_pow, radix, half]
    have small : 18446744073709551616 - 1 - word.toNat < 9223372036854775808 := by omega
    rw [Nat.div_eq_of_lt small, if_pos negative]
  · have sign : word.toBitVec.msb=false := by rw [msb]; exact decide_eq_false negative
    rw [BitVec.toNat_sshiftRight_of_msb_false sign, UInt64.toNat_toBitVec,
      Nat.shiftRight_eq_div_pow, half, Nat.div_eq_of_lt (by omega), if_neg negative]

theorem original_coded_factor_arithmetic_shift_mask_matches_the_integer_sign
    (value : Int) (lower : -9223372036854775808 <= value) (upper : value < 9223372036854775808) :
    (sourceFactorSignMask (sourceSignedWordCode value)).toNat =
      if value < 0 then 18446744073709551615 else 0 := by
  simp only [original_factor_arithmetic_shift_by_63_is_the_exact_zero_or_all_ones_mask,
    TransferBlstArmInverseSignedWord01.original_unsigned_factor_sign_threshold_is_exact_integer_negativity value lower upper]

theorem original_factor_arithmetic_shift_mask_is_the_exact_word_constant (word : UInt64) :
    sourceFactorSignMask word =
      if 9223372036854775808 <= word.toNat then (-1:UInt64) else 0 := by
  apply UInt64.toNat_inj.mp
  rw [original_factor_arithmetic_shift_by_63_is_the_exact_zero_or_all_ones_mask]
  have ones : (-1:UInt64).toNat=18446744073709551615 := by decide
  by_cases negative : 9223372036854775808 <= word.toNat
  · simp only [if_pos negative, ones]
  · simp only [if_neg negative, UInt64.toNat_zero]

set_option pp.all true in
#check @sourceFactorSignMask
#print axioms sourceFactorSignMask
set_option pp.all true in
#check @original_factor_arithmetic_shift_by_63_is_the_exact_zero_or_all_ones_mask
#print axioms original_factor_arithmetic_shift_by_63_is_the_exact_zero_or_all_ones_mask
set_option pp.all true in
#check @original_coded_factor_arithmetic_shift_mask_matches_the_integer_sign
#print axioms original_coded_factor_arithmetic_shift_mask_matches_the_integer_sign
set_option pp.all true in
#check @original_factor_arithmetic_shift_mask_is_the_exact_word_constant
#print axioms original_factor_arithmetic_shift_mask_is_the_exact_word_constant
end ShielddSecurity.TransferBlstArmInverseSignMask01
