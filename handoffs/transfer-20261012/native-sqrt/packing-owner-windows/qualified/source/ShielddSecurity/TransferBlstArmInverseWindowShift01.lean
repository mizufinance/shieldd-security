import Init.Data.UInt.Lemmas
import Init.Data.BitVec.Lemmas
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowShift01

/-! Mac import-minimized replay variant of the desktop handwritten draft for the NEG/LSRV/ASR6 part of the locked
high-window approximation. The bounded shift count is explicit. The runtime
CLZ/limb-selection producer and compiled instruction correspondence are open. -/

def sourceWindowNegativeCount (count : Nat) : UInt64 := -UInt64.ofNat count

def sourceWindowLowMask (count : Nat) : UInt64 :=
  UInt64.ofBitVec ((sourceWindowNegativeCount count).toBitVec.sshiftRight 6)

theorem bounded_window_shift_count_has_its_entire_unsigned_word_value
    (count : Nat) (bounded : count < 64) :
    (UInt64.ofNat count).toNat = count := by
  apply UInt64.toNat_ofNat_of_lt'
  change count < 18446744073709551616
  omega

theorem original_window_negated_shift_count_has_the_exact_unsigned_residue
    (count : Nat) (bounded : count < 64) :
    (sourceWindowNegativeCount count).toNat =
      if count = 0 then 0 else 18446744073709551616 - count := by
  rw [sourceWindowNegativeCount, UInt64.toNat_neg,
    bounded_window_shift_count_has_its_entire_unsigned_word_value count bounded]
  have radix : UInt64.size = 18446744073709551616 := by rfl
  rw [radix]
  by_cases zero : count = 0
  · simp only [zero, Nat.sub_zero, Nat.mod_self, if_true]
  · rw [if_neg zero, Nat.mod_eq_of_lt (by omega)]

theorem original_window_negated_count_has_the_exact_lsrv_shift_distance
    (count : Nat) (bounded : count < 64) :
    (sourceWindowNegativeCount count).toNat % 64 =
      if count = 0 then 0 else 64 - count := by
  rw [original_window_negated_shift_count_has_the_exact_unsigned_residue count bounded]
  by_cases zero : count = 0
  · simp only [if_pos zero, Nat.zero_mod]
  · simp only [if_neg zero]
    omega

theorem original_window_asr6_mask_is_exactly_zero_or_all_ones
    (count : Nat) (bounded : count < 64) :
    (sourceWindowLowMask count).toNat =
      if count = 0 then 0 else 18446744073709551615 := by
  rw [sourceWindowLowMask, UInt64.toNat_ofBitVec]
  have radix : (2 : Nat) ^ 64 = 18446744073709551616 := by decide +kernel
  have half : (2 : Nat) ^ 63 = 9223372036854775808 := by decide +kernel
  have distance : (2 : Nat) ^ 6 = 64 := by decide
  have residue := original_window_negated_shift_count_has_the_exact_unsigned_residue count bounded
  by_cases zero : count = 0
  · have empty : sourceWindowNegativeCount count = 0 := by
      apply UInt64.toNat_inj.mp
      simpa only [if_pos zero, UInt64.toNat_zero] using residue
    simp only [empty, UInt64.toBitVec_zero, BitVec.zero_sshiftRight,
      BitVec.toNat_zero, if_pos zero]
  · have value : (sourceWindowNegativeCount count).toNat = 18446744073709551616 - count := by
      simpa only [if_neg zero] using residue
    have negative : (sourceWindowNegativeCount count).toBitVec.msb = true := by
      rw [BitVec.msb_eq_decide, UInt64.toNat_toBitVec, half, value]
      exact decide_eq_true (by omega)
    rw [BitVec.toNat_sshiftRight_of_msb_true negative, UInt64.toNat_toBitVec,
      Nat.shiftRight_eq_div_pow, radix, distance, value, if_neg zero,
      Nat.div_eq_of_lt (by omega : 18446744073709551616 - 1 -
        (18446744073709551616 - count) < 64)]

theorem original_window_asr6_mask_is_the_exact_unsigned_word_constant
    (count : Nat) (bounded : count < 64) :
    sourceWindowLowMask count = if count = 0 then 0 else (-1 : UInt64) := by
  apply UInt64.toNat_inj.mp
  rw [original_window_asr6_mask_is_exactly_zero_or_all_ones count bounded]
  by_cases zero : count = 0
  · simp only [if_pos zero, UInt64.toNat_zero]
  · have ones : (-1 : UInt64).toNat = 18446744073709551615 := by decide
    simp only [if_neg zero, ones]

theorem original_window_lsrv_of_the_low_limb_has_the_exact_nat_quotient
    (count : Nat) (low : UInt64) (bounded : count < 64) (positive : 0 < count) :
    (low >>> sourceWindowNegativeCount count).toNat = low.toNat / 2 ^ (64 - count) := by
  rw [UInt64.toNat_shiftRight,
    original_window_negated_count_has_the_exact_lsrv_shift_distance count bounded,
    if_neg (by omega : count ≠ 0), Nat.shiftRight_eq_div_pow]

set_option pp.all true in
#check @sourceWindowNegativeCount
#print axioms sourceWindowNegativeCount
set_option pp.all true in
#check @sourceWindowLowMask
#print axioms sourceWindowLowMask
set_option pp.all true in
#check @bounded_window_shift_count_has_its_entire_unsigned_word_value
#print axioms bounded_window_shift_count_has_its_entire_unsigned_word_value
set_option pp.all true in
#check @original_window_negated_shift_count_has_the_exact_unsigned_residue
#print axioms original_window_negated_shift_count_has_the_exact_unsigned_residue
set_option pp.all true in
#check @original_window_negated_count_has_the_exact_lsrv_shift_distance
#print axioms original_window_negated_count_has_the_exact_lsrv_shift_distance
set_option pp.all true in
#check @original_window_asr6_mask_is_exactly_zero_or_all_ones
#print axioms original_window_asr6_mask_is_exactly_zero_or_all_ones
set_option pp.all true in
#check @original_window_asr6_mask_is_the_exact_unsigned_word_constant
#print axioms original_window_asr6_mask_is_the_exact_unsigned_word_constant
set_option pp.all true in
#check @original_window_lsrv_of_the_low_limb_has_the_exact_nat_quotient
#print axioms original_window_lsrv_of_the_low_limb_has_the_exact_nat_quotient
end ShielddSecurity.TransferBlstArmInverseWindowShift01
