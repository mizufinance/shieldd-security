import ShielddSecurity.TransferBlstArmInverseWindowSelect01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowJoint01
open TransferBlstArmInverseWindowSelect01
open TransferBlstArmInverseWindowClz01

/-! UNRUN handwritten selection/CLZ zero-branch correspondence. This connects
the actual modeled CLZ64 condition to the three original upper joint words,
without using a desired quotient or output value as a premise. -/

theorem original_joint_clz_count_is_64_exactly_when_the_joint_high_word_is_zero
    (highA highB : UInt64) :
    (highA ||| highB).toBitVec.clz.toNat = 64 ↔ highA ||| highB = 0 := by
  constructor
  · intro count
    have wordCount : (highA ||| highB).toBitVec.clz = (64 : BitVec 64) := by
      apply BitVec.toNat_inj.mp
      change (highA ||| highB).toBitVec.clz.toNat = 64
      exact count
    have zeroBits := BitVec.clz_eq_iff_eq_zero.mp wordCount
    apply UInt64.toBitVec_inj.mp
    simpa only [UInt64.toBitVec_zero] using zeroBits
  · intro zero
    have zeroBits : (highA ||| highB).toBitVec = 0#64 := by rw [zero, UInt64.toBitVec_zero]
    have count := congrArg BitVec.toNat (BitVec.clz_eq_iff_eq_zero.mpr zeroBits)
    change (highA ||| highB).toBitVec.clz.toNat = 64 at count
    exact count

theorem original_nonzero_joint_high_window_retains_the_selected_high_words_and_raw_clz
    (highA highB lowA lowB : UInt64) (nonzero : highA ||| highB ≠ 0) :
    sourceCommonWindow highA highB lowA lowB =
      ⟨highA, highB, (highA ||| highB).toBitVec.clz.toNat⟩ := by
  have active : (highA ||| highB).toBitVec.clz.toNat ≠ 64 := by
    intro zeroCount
    exact nonzero ((original_joint_clz_count_is_64_exactly_when_the_joint_high_word_is_zero highA highB).mp zeroCount)
  simp only [sourceCommonWindow, if_neg active]

theorem original_selected_joint_window_is_zero_exactly_when_all_original_upper_joint_words_are_zero
    (a b : SourceFourWords) :
    let selected := sourceSecondWindowChoice a b
    selected.highA ||| selected.highB = 0 ↔
      (a.w3 ||| b.w3 = 0 ∧ a.w2 ||| b.w2 = 0 ∧ a.w1 ||| b.w1 = 0) := by
  rw [original_two_staged_choices_select_the_joint_highest_upper_window]
  by_cases top : (a.w3 ||| b.w3) ≠ 0
  · rw [if_pos top]
    constructor
    · intro zero
      exact False.elim (top zero)
    · intro all
      exact all.1
  · rw [if_neg top]
    by_cases middle : (a.w2 ||| b.w2) ≠ 0
    · rw [if_pos middle]
      constructor
      · intro zero
        exact False.elim (middle zero)
      · intro all
        exact all.2.1
    · rw [if_neg middle]
      exact ⟨fun zero => ⟨not_ne_iff.mp top, not_ne_iff.mp middle, zero⟩,
        fun all => all.2.2⟩

end ShielddSecurity.TransferBlstArmInverseWindowJoint01
