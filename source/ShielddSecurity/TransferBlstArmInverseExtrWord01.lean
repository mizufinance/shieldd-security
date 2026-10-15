import ShielddSecurity.TransferBlstArmInverseSignedProductDecode01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseExtrWord01

/-! Arithmetic model of a nonzero EXTR immediate through actual UInt64
left/right shifts and OR. The high word may overflow its shifted window;
its exact retained remainder is derived. Native EXTR execution is separate. -/

def sourceExtractWord (high low : UInt64) (shift : Nat) : UInt64 :=
  (high <<< UInt64.ofNat (64 - shift)) ||| (low >>> UInt64.ofNat shift)

theorem original_extr_left_fragment_retains_the_exact_high_word_remainder
    (high : UInt64) (shift : Nat) (positive : 0 < shift) (bounded : shift < 64) :
    (high <<< UInt64.ofNat (64 - shift)).toNat = 2 ^ (64 - shift) * (high.toNat % 2 ^ shift) := by
  have leftBound : 64 - shift < 64 := by omega
  have factorization : (2 : Nat) ^ 64 = 2 ^ shift * 2 ^ (64 - shift) := by
    rw [←Nat.pow_add, show shift + (64 - shift) = 64 by omega]
  rw [UInt64.toNat_shiftLeft,
    TransferBlstArmInverseWindowShift01.bounded_window_shift_count_has_its_entire_unsigned_word_value (64 - shift) leftBound,
    Nat.mod_eq_of_lt leftBound, Nat.shiftLeft_eq, factorization, Nat.mul_mod_mul_right]
  exact Nat.mul_comm _ _

theorem original_extr_right_fragment_is_the_entire_low_word_quotient
    (low : UInt64) (shift : Nat) (bounded : shift < 64) :
    (low >>> UInt64.ofNat shift).toNat = low.toNat / 2 ^ shift := by
  rw [UInt64.toNat_shiftRight,
    TransferBlstArmInverseWindowShift01.bounded_window_shift_count_has_its_entire_unsigned_word_value shift bounded,
    Nat.mod_eq_of_lt bounded, Nat.shiftRight_eq_div_pow]

theorem original_extr_word_derives_both_entire_nonoverlapping_window_fragments
    (high low : UInt64) (shift : Nat) (positive : 0 < shift) (bounded : shift < 64) :
    (sourceExtractWord high low shift).toNat =
      2 ^ (64 - shift) * (high.toNat % 2 ^ shift) + low.toNat / 2 ^ shift := by
  have factorization : (2 : Nat) ^ (64 - shift) * 2 ^ shift = 2 ^ 64 := by
    rw [←Nat.pow_add, show (64 - shift) + shift = 64 by omega]
  have lowBound : low.toNat / 2 ^ shift < 2 ^ (64 - shift) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)).mpr
    rw [factorization]
    exact low.toNat_lt
  rw [sourceExtractWord, UInt64.toNat_or,
    original_extr_left_fragment_retains_the_exact_high_word_remainder high shift positive bounded,
    original_extr_right_fragment_is_the_entire_low_word_quotient low shift bounded]
  exact TransferBlstArmInverseWindowArithmetic01.symbolic_disjoint_window_fragments_have_exact_or_sum
    (64 - shift) (high.toNat % 2 ^ shift) (low.toNat / 2 ^ shift) lowBound

set_option pp.all true in
#check @sourceExtractWord
#print axioms sourceExtractWord
set_option pp.all true in
#check @original_extr_left_fragment_retains_the_exact_high_word_remainder
#print axioms original_extr_left_fragment_retains_the_exact_high_word_remainder
set_option pp.all true in
#check @original_extr_right_fragment_is_the_entire_low_word_quotient
#print axioms original_extr_right_fragment_is_the_entire_low_word_quotient
set_option pp.all true in
#check @original_extr_word_derives_both_entire_nonoverlapping_window_fragments
#print axioms original_extr_word_derives_both_entire_nonoverlapping_window_fragments
end ShielddSecurity.TransferBlstArmInverseExtrWord01
