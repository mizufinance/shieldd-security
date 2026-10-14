import ShielddSecurity.TransferBlstArmInverseWindowArithmetic01
import ShielddSecurity.TransferBlstArmInverseWindowShift01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowAlign01
open TransferBlstArmInverseWindowShift01

/-! Mac import-minimized replay variant of the desktop handwritten composition of the locked LSLV/LSRV/ASR6/AND/OR
window arithmetic. The selected high-limb bound and full-input decomposition
are explicit producer obligations. CLZ, common limb selection, packed-input
correspondence and compiled execution have not been established here. -/

def sourceAlignedWindowWord (high low : UInt64) (count : Nat) : UInt64 :=
  (high <<< UInt64.ofNat count) |||
    ((low >>> sourceWindowNegativeCount count) &&& sourceWindowLowMask count)

theorem original_window_left_shift_has_no_overflow_under_the_selected_limb_bound
    (high : UInt64) (count : Nat) (bounded : count < 64)
    (highBound : high.toNat < 2 ^ (64 - count)) :
    (high <<< UInt64.ofNat count).toNat = 2 ^ count * high.toNat := by
  have factorization : (2 : Nat) ^ count * 2 ^ (64 - count) = 2 ^ 64 := by
    rw [← Nat.pow_add, show count + (64 - count) = 64 by omega]
  have fits : 2 ^ count * high.toNat < 2 ^ 64 := by
    rw [← factorization]
    exact Nat.mul_lt_mul_of_pos_left highBound (Nat.two_pow_pos count)
  rw [UInt64.toNat_shiftLeft,
    bounded_window_shift_count_has_its_entire_unsigned_word_value count bounded,
    Nat.mod_eq_of_lt bounded, Nat.shiftLeft_eq,
    Nat.mul_comm high.toNat (2 ^ count), Nat.mod_eq_of_lt fits]

theorem original_masked_window_low_shift_has_the_exact_quotient_including_zero_count
    (low : UInt64) (count : Nat) (bounded : count < 64) :
    ((low >>> sourceWindowNegativeCount count) &&& sourceWindowLowMask count).toNat =
      low.toNat / 2 ^ (64 - count) := by
  rw [original_window_asr6_mask_is_the_exact_unsigned_word_constant count bounded]
  by_cases zero : count = 0
  · have lowBound : low.toNat < (2 : Nat) ^ 64 := low.toNat_lt
    simp only [UInt64.and_zero, UInt64.toNat_zero, zero, Nat.sub_zero,
      Nat.div_eq_of_lt lowBound, if_true]
  · rw [if_neg zero, UInt64.and_neg_one]
    exact original_window_lsrv_of_the_low_limb_has_the_exact_nat_quotient
      count low bounded (by omega)

theorem original_aligned_window_word_has_its_entire_exact_nat_value
    (high low : UInt64) (count : Nat) (bounded : count < 64)
    (highBound : high.toNat < 2 ^ (64 - count)) :
    (sourceAlignedWindowWord high low count).toNat =
      2 ^ count * high.toNat + low.toNat / 2 ^ (64 - count) := by
  have factorization : (2 : Nat) ^ count * 2 ^ (64 - count) = 2 ^ 64 := by
    rw [← Nat.pow_add, show count + (64 - count) = 64 by omega]
  have disjoint : low.toNat / 2 ^ (64 - count) < 2 ^ count := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (64 - count))).2
    rw [factorization]
    exact low.toNat_lt
  rw [sourceAlignedWindowWord, UInt64.toNat_or,
    original_window_left_shift_has_no_overflow_under_the_selected_limb_bound high count bounded highBound,
    original_masked_window_low_shift_has_the_exact_quotient_including_zero_count low count bounded]
  exact (Nat.two_pow_add_eq_or_of_lt disjoint high.toNat).symm

theorem original_aligned_window_word_matches_the_whole_input_quotient_from_an_explicit_prefix
    (high low : UInt64) (count base tail input : Nat)
    (bounded : count < 64) (highBound : high.toNat < 2 ^ (64 - count))
    (basePositive : 0 < base) (tailBound : tail < base)
    (representation : input = base * (2 ^ 64 * high.toNat + low.toNat) + tail) :
    (sourceAlignedWindowWord high low count).toNat = input / (base * 2 ^ (64 - count)) := by
  have factorization : (2 : Nat) ^ 64 = 2 ^ count * 2 ^ (64 - count) := by
    rw [← Nat.pow_add, show count + (64 - count) = 64 by omega]
  rw [original_aligned_window_word_has_its_entire_exact_nat_value high low count bounded highBound,
    representation]
  exact (TransferBlstArmInverseWindowArithmetic01.symbolic_whole_input_window_division_removes_all_lower_limbs
    base (2 ^ 64) (2 ^ count) (2 ^ (64 - count)) high.toNat low.toNat tail
    basePositive (Nat.two_pow_pos (64 - count)) tailBound factorization).symm

set_option pp.all true in
#check @sourceAlignedWindowWord
#print axioms sourceAlignedWindowWord
set_option pp.all true in
#check @original_window_left_shift_has_no_overflow_under_the_selected_limb_bound
#print axioms original_window_left_shift_has_no_overflow_under_the_selected_limb_bound
set_option pp.all true in
#check @original_masked_window_low_shift_has_the_exact_quotient_including_zero_count
#print axioms original_masked_window_low_shift_has_the_exact_quotient_including_zero_count
set_option pp.all true in
#check @original_aligned_window_word_has_its_entire_exact_nat_value
#print axioms original_aligned_window_word_has_its_entire_exact_nat_value
set_option pp.all true in
#check @original_aligned_window_word_matches_the_whole_input_quotient_from_an_explicit_prefix
#print axioms original_aligned_window_word_matches_the_whole_input_quotient_from_an_explicit_prefix
end ShielddSecurity.TransferBlstArmInverseWindowAlign01
