import ShielddSecurity.TransferBlstArmInverseFullWidth01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWidthBudget01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords sourceSecondWindowChoice)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowShift)
open TransferBlstArmInverseFullWidth01 (sourceClippedJointBitwidth)

/-! UNRUN exact four-word initial width budget. The original staged selector
chooses index1,2 or3, bounding its computed shift and joint width. Complete
input log2 sizes derive an initial sum budget of512. This does not yet prove
the source31-step pair-size decrease or native schedule correspondence. -/

theorem original_staged_selection_always_returns_an_index_between_one_and_three
    (a b : SourceFourWords) :
    1 ≤ (sourceSecondWindowChoice a b).index ∧ (sourceSecondWindowChoice a b).index ≤ 3 := by
  rw [TransferBlstArmInverseWindowSelect01.original_two_staged_choices_select_the_joint_highest_upper_window]
  by_cases top : (a.w3 ||| b.w3) ≠ 0
  · rw [if_pos top]
    change 1 ≤ 3 ∧ 3 ≤ 3
    exact ⟨by decide, by decide⟩
  · rw [if_neg top]
    by_cases middle : (a.w2 ||| b.w2) ≠ 0
    · rw [if_pos middle]
      change 1 ≤ 2 ∧ 2 ≤ 3
      exact ⟨by decide, by decide⟩
    · rw [if_neg middle]
      change 1 ≤ 1 ∧ 1 ≤ 3
      exact ⟨by decide, by decide⟩

theorem original_four_word_source_window_shift_is_at_most192
    (a b : SourceFourWords) : sourceFourWordWindowShift a b ≤ 192 := by
  have indices := original_staged_selection_always_returns_an_index_between_one_and_three a b
  dsimp only [sourceFourWordWindowShift]
  split
  · decide
  · omega

theorem original_full_input_joint_bitwidth_is_between64_and256
    (a b : SourceFourWords) : 64 ≤ sourceClippedJointBitwidth a b ∧ sourceClippedJointBitwidth a b ≤ 256 := by
  constructor
  · exact Nat.le_max_left _ _
  · have shift := original_four_word_source_window_shift_is_at_most192 a b
    have width := TransferBlstArmInverseFullWidth01.original_computed_shift_plus64_is_the_exact_clipped_full_input_joint_bitwidth a b
    omega

theorem original_complete_four_word_inputs_have_initial_log2_size_sum_at_most512
    (a b : SourceFourWords) :
    ((sourcePackedFourWords a).log2 + 1) + ((sourcePackedFourWords b).log2 + 1) ≤ 512 := by
  have bound := (original_full_input_joint_bitwidth_is_between64_and256 a b).2
  change max 64 (max ((sourcePackedFourWords a).log2 + 1) ((sourcePackedFourWords b).log2 + 1)) ≤ 256 at bound
  have both := Nat.max_le.mp (Nat.max_le.mp bound).2
  omega

set_option pp.all true in
#check @original_staged_selection_always_returns_an_index_between_one_and_three
#print axioms original_staged_selection_always_returns_an_index_between_one_and_three
set_option pp.all true in
#check @original_four_word_source_window_shift_is_at_most192
#print axioms original_four_word_source_window_shift_is_at_most192
set_option pp.all true in
#check @original_full_input_joint_bitwidth_is_between64_and256
#print axioms original_full_input_joint_bitwidth_is_between64_and256
set_option pp.all true in
#check @original_complete_four_word_inputs_have_initial_log2_size_sum_at_most512
#print axioms original_complete_four_word_inputs_have_initial_log2_size_sum_at_most512
end ShielddSecurity.TransferBlstArmInverseWidthBudget01
