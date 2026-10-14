import ShielddSecurity.TransferBlstArmInverseWindowSelect01
import Mathlib.Tactic.Ring.Basic
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowPrefix01
open TransferBlstArmInverseWindowSelect01
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)

/-! UNRUN handwritten full-input prefixes for every selected upper window.
The tail bounds are derived from raw UInt64 packing. These are the register
values before CLZ64 fallback; replacing a selected high word requires the
separate one-word argument. Native load/CSEL/ABI correspondence remains open. -/

def sourceSelectedLowerTail (a : SourceFourWords) (index : Nat) : Nat :=
  if index = 3 then packWords [a.w0, a.w1]
  else if index = 2 then a.w0.toNat else 0

theorem original_top_window_has_its_entire_input_prefix_and_bounded_two_word_tail
    (a : SourceFourWords) :
    sourcePackedFourWords a = radix64 ^ 2 * (radix64 * a.w3.toNat + a.w2.toNat) +
        packWords [a.w0, a.w1] ∧ packWords [a.w0, a.w1] < radix64 ^ 2 := by
  constructor
  · simp only [sourcePackedFourWords, packWords, Nat.mul_zero, Nat.add_zero, Nat.pow_two]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm]
  · simpa only [List.length_cons, List.length_nil] using
      (TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power [a.w0, a.w1])

theorem original_middle_window_has_its_entire_input_prefix_and_bounded_one_word_tail
    (a : SourceFourWords) (topZero : a.w3 = 0) :
    sourcePackedFourWords a = radix64 * (radix64 * a.w2.toNat + a.w1.toNat) + a.w0.toNat ∧
      a.w0.toNat < radix64 := by
  constructor
  · simp only [sourcePackedFourWords, packWords, topZero, UInt64.toNat_zero,
      Nat.mul_zero, Nat.add_zero]
    ring1
  · exact a.w0.toNat_lt

theorem original_lower_window_has_its_entire_input_prefix_and_zero_tail
    (a : SourceFourWords) (middleZero : a.w2 = 0) (topZero : a.w3 = 0) :
    sourcePackedFourWords a = radix64 * a.w1.toNat + a.w0.toNat ∧ (0 : Nat) < 1 := by
  constructor
  · simp only [sourcePackedFourWords, packWords, middleZero, topZero, UInt64.toNat_zero,
      Nat.mul_zero, Nat.add_zero]
    ring1
  · decide

theorem original_staged_selection_derives_both_entire_input_prefixes_and_tail_bounds
    (a b : SourceFourWords) :
    let selected := sourceSecondWindowChoice a b
    let base := radix64 ^ (selected.index - 1)
    sourcePackedFourWords a = base * (radix64 * selected.highA.toNat + selected.lowA.toNat) +
        sourceSelectedLowerTail a selected.index ∧
      sourcePackedFourWords b = base * (radix64 * selected.highB.toNat + selected.lowB.toNat) +
        sourceSelectedLowerTail b selected.index ∧
      sourceSelectedLowerTail a selected.index < base ∧ sourceSelectedLowerTail b selected.index < base := by
  rw [original_two_staged_choices_select_the_joint_highest_upper_window]
  by_cases top : (a.w3 ||| b.w3) ≠ 0
  · rw [if_pos top]
    change sourcePackedFourWords a = radix64 ^ 2 * (radix64 * a.w3.toNat + a.w2.toNat) + packWords [a.w0, a.w1] ∧
      sourcePackedFourWords b = radix64 ^ 2 * (radix64 * b.w3.toNat + b.w2.toNat) + packWords [b.w0, b.w1] ∧
      packWords [a.w0, a.w1] < radix64 ^ 2 ∧ packWords [b.w0, b.w1] < radix64 ^ 2
    have left := original_top_window_has_its_entire_input_prefix_and_bounded_two_word_tail a
    have right := original_top_window_has_its_entire_input_prefix_and_bounded_two_word_tail b
    exact ⟨left.1, right.1, left.2, right.2⟩
  · rw [if_neg top]
    have topWords := UInt64.or_eq_zero_iff.mp (Classical.not_not.mp top)
    by_cases middle : (a.w2 ||| b.w2) ≠ 0
    · rw [if_pos middle]
      change sourcePackedFourWords a = radix64 * (radix64 * a.w2.toNat + a.w1.toNat) + a.w0.toNat ∧
        sourcePackedFourWords b = radix64 * (radix64 * b.w2.toNat + b.w1.toNat) + b.w0.toNat ∧
        a.w0.toNat < radix64 ∧ b.w0.toNat < radix64
      have left := original_middle_window_has_its_entire_input_prefix_and_bounded_one_word_tail a topWords.1
      have right := original_middle_window_has_its_entire_input_prefix_and_bounded_one_word_tail b topWords.2
      exact ⟨left.1, right.1, left.2, right.2⟩
    · rw [if_neg middle]
      have middleWords := UInt64.or_eq_zero_iff.mp (Classical.not_not.mp middle)
      change sourcePackedFourWords a = 1 * (radix64 * a.w1.toNat + a.w0.toNat) + 0 ∧
        sourcePackedFourWords b = 1 * (radix64 * b.w1.toNat + b.w0.toNat) + 0 ∧
        (0 : Nat) < 1 ∧ (0 : Nat) < 1
      have left := original_lower_window_has_its_entire_input_prefix_and_zero_tail a middleWords.1 topWords.1
      have right := original_lower_window_has_its_entire_input_prefix_and_zero_tail b middleWords.2 topWords.2
      simpa only [Nat.one_mul, Nat.add_zero] using
        (show sourcePackedFourWords a = radix64 * a.w1.toNat + a.w0.toNat ∧
          sourcePackedFourWords b = radix64 * b.w1.toNat + b.w0.toNat ∧
          (0 : Nat) < 1 ∧ (0 : Nat) < 1 from ⟨left.1, right.1, left.2, right.2⟩)

set_option pp.all true in
#check @sourceSelectedLowerTail
#print axioms sourceSelectedLowerTail
set_option pp.all true in
#check @original_top_window_has_its_entire_input_prefix_and_bounded_two_word_tail
#print axioms original_top_window_has_its_entire_input_prefix_and_bounded_two_word_tail
set_option pp.all true in
#check @original_middle_window_has_its_entire_input_prefix_and_bounded_one_word_tail
#print axioms original_middle_window_has_its_entire_input_prefix_and_bounded_one_word_tail
set_option pp.all true in
#check @original_lower_window_has_its_entire_input_prefix_and_zero_tail
#print axioms original_lower_window_has_its_entire_input_prefix_and_zero_tail
set_option pp.all true in
#check @original_staged_selection_derives_both_entire_input_prefixes_and_tail_bounds
#print axioms original_staged_selection_derives_both_entire_input_prefixes_and_tail_bounds
end ShielddSecurity.TransferBlstArmInverseWindowPrefix01
