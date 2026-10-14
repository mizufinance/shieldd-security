import ShielddSecurity.TransferBlstArmInverseJointPower01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseFullWindowBounds01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords sourceSecondWindowChoice)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowShift)
open TransferBlstArmInverseWindowPrefix01 (sourceSelectedLowerTail)
open TransferScalarSerializationRange01 (radix64)

/-! UNRUN complete-input lower power for the original nonzero selected upper
window, plus exact zero-window shift. All prefix and joint CLZ facts derive
from the source selection and original words. Exact clipped joint width and
31-bit progress composition follow separately; native execution stays open. -/

theorem original_nonzero_raw_joint_clz_count_is_strictly_below64
    (highA highB : UInt64) (nonzero : highA ||| highB ≠ 0) :
    (highA ||| highB).toBitVec.clz.toNat < 64 := by
  have bounds := TransferBlstArmInverseWindowClz01.original_common_clz_window_derives_both_high_bounds_and_a_bounded_count
    highA highB 0 0
  have retained := TransferBlstArmInverseWindowJoint01.original_nonzero_joint_high_window_retains_the_selected_high_words_and_raw_clz
    highA highB 0 0 nonzero
  rw [retained] at bounds
  exact bounds.1

theorem original_nonzero_selected_upper_window_derives_a_full_input_lower_power
    (a b : SourceFourWords)
    (nonzero : (sourceSecondWindowChoice a b).highA ||| (sourceSecondWindowChoice a b).highB ≠ 0) :
    2 ^ (sourceFourWordWindowShift a b + 63) ≤ sourcePackedFourWords a ∨
      2 ^ (sourceFourWordWindowShift a b + 63) ≤ sourcePackedFourWords b := by
  let selected := sourceSecondWindowChoice a b
  let count := (selected.highA ||| selected.highB).toBitVec.clz.toNat
  let baseExponent := 64 * (selected.index - 1)
  have countBound : count < 64 := original_nonzero_raw_joint_clz_count_is_strictly_below64 _ _ nonzero
  have retained := TransferBlstArmInverseWindowJoint01.original_nonzero_joint_high_window_retains_the_selected_high_words_and_raw_clz
    selected.highA selected.highB selected.lowA selected.lowB nonzero
  have shift : sourceFourWordWindowShift a b = baseExponent + (64 - count) := by
    dsimp only [sourceFourWordWindowShift]
    rw [if_neg nonzero, retained]
  have exponent : baseExponent + 64 + (63 - count) = sourceFourWordWindowShift a b + 63 := by
    rw [shift]
    omega
  have originals := TransferBlstArmInverseWindowPrefix01.original_staged_selection_derives_both_entire_input_prefixes_and_tail_bounds a b
  have leftPrefix : sourcePackedFourWords a = 2 ^ baseExponent *
      (2 ^ 64 * selected.highA.toNat + selected.lowA.toNat) + sourceSelectedLowerTail a selected.index := by
    simpa only [baseExponent, radix64, ←Nat.pow_mul] using originals.1
  have rightPrefix : sourcePackedFourWords b = 2 ^ baseExponent *
      (2 ^ 64 * selected.highB.toNat + selected.lowB.toNat) + sourceSelectedLowerTail b selected.index := by
    simpa only [baseExponent, radix64, ←Nat.pow_mul] using originals.2.1
  have highLower : 2 ^ (63 - count) ≤ selected.highA.toNat ∨ 2 ^ (63 - count) ≤ selected.highB.toNat :=
    TransferBlstArmInverseJointPower01.original_nonzero_joint_clz_derives_a_high_word_with_its_exact_lower_power _ _ nonzero
  rcases highLower with left | right
  · left
    have bound := TransferBlstArmInverseJointPower01.exact_full_input_prefix_lifts_the_high_word_lower_power
      _ _ _ _ _ _ leftPrefix left
    rw [exponent] at bound
    exact bound
  · right
    have bound := TransferBlstArmInverseJointPower01.exact_full_input_prefix_lifts_the_high_word_lower_power
      _ _ _ _ _ _ rightPrefix right
    rw [exponent] at bound
    exact bound

theorem original_zero_selected_upper_window_has_exactly_zero_source_shift
    (a b : SourceFourWords)
    (zero : (sourceSecondWindowChoice a b).highA ||| (sourceSecondWindowChoice a b).highB = 0) :
    sourceFourWordWindowShift a b = 0 := by
  simp only [sourceFourWordWindowShift, if_pos zero]

set_option pp.all true in
#check @original_nonzero_raw_joint_clz_count_is_strictly_below64
#print axioms original_nonzero_raw_joint_clz_count_is_strictly_below64
set_option pp.all true in
#check @original_nonzero_selected_upper_window_derives_a_full_input_lower_power
#print axioms original_nonzero_selected_upper_window_derives_a_full_input_lower_power
set_option pp.all true in
#check @original_zero_selected_upper_window_has_exactly_zero_source_shift
#print axioms original_zero_selected_upper_window_has_exactly_zero_source_shift
end ShielddSecurity.TransferBlstArmInverseFullWindowBounds01
