import ShielddSecurity.TransferBlstArmInverseFinalCases01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowMagnitude01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)

/-! UNRUN source-selected window magnitude development. Exact whole-input
quotients and bounded UInt64 words derive a full-input upper power bound.
The actual joint CLZ derives its raw high-word magnitude interval. Matching
the full joint lower bound, exact bitlength width and total progress remains
separate; no native caller or compiled instruction correspondence asserted. -/

theorem exact_entire_input_uint64_quotient_bounds_the_entire_input_magnitude
    (input shift : Nat) (high : UInt64) (window : high.toNat = input / 2 ^ shift) :
    input < 2 ^ (shift + 64) := by
  have quotient : input / 2 ^ shift < 2 ^ 64 := by
    rw [←window]
    exact high.toNat_lt
  have bound := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)).mp quotient
  rw [Nat.pow_add, Nat.mul_comm]
  exact bound

theorem original_source_selected_window_derives_both_full_input_upper_power_bounds
    (a b : SourceFourWords) :
    sourcePackedFourWords a < 2 ^ (sourceFourWordWindowShift a b + 64) ∧
      sourcePackedFourWords b < 2 ^ (sourceFourWordWindowShift a b + 64) := by
  have windows := TransferBlstArmInverseWindowInput01.original_source_window_words_derive_the_high_window_premises_for_both_entire_inputs a b
  exact ⟨exact_entire_input_uint64_quotient_bounds_the_entire_input_magnitude _ _ _ windows.1,
    exact_entire_input_uint64_quotient_bounds_the_entire_input_magnitude _ _ _ windows.2⟩

theorem original_nonzero_joint_clz_derives_the_exact_raw_word_power_interval
    (highA highB : UInt64) (nonzero : highA ||| highB ≠ 0) :
    let count := (highA ||| highB).toBitVec.clz.toNat
    2 ^ (63 - count) ≤ (highA ||| highB).toNat ∧
      (highA ||| highB).toNat < 2 ^ (64 - count) := by
  dsimp only
  have bitsNonzero : (highA ||| highB).toBitVec ≠ 0#64 := by
    intro zero
    apply nonzero
    apply UInt64.toBitVec_inj.mp
    simpa only [UInt64.toBitVec_zero] using zero
  have lower := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by decide : 0 < 64) bitsNonzero
  have upper := BitVec.toNat_lt_two_pow_sub_clz (x := (highA ||| highB).toBitVec)
  exact ⟨lower, upper⟩

set_option pp.all true in
#check @exact_entire_input_uint64_quotient_bounds_the_entire_input_magnitude
#print axioms exact_entire_input_uint64_quotient_bounds_the_entire_input_magnitude
set_option pp.all true in
#check @original_source_selected_window_derives_both_full_input_upper_power_bounds
#print axioms original_source_selected_window_derives_both_full_input_upper_power_bounds
set_option pp.all true in
#check @original_nonzero_joint_clz_derives_the_exact_raw_word_power_interval
#print axioms original_nonzero_joint_clz_derives_the_exact_raw_word_power_interval
end ShielddSecurity.TransferBlstArmInverseWindowMagnitude01
