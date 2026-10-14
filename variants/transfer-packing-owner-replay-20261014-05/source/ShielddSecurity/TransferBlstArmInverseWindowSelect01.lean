import ShielddSecurity.TransferBlstArmInverseWindowClz01
import ShielddSecurity.TransferScalarWordPrimitives01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowSelect01
open TransferBlstArmInverseWindowClz01
open TransferBlstArmInverseWindowAlign01 (sourceAlignedWindowWord)
open TransferScalarWordPrimitives01 (packWords)

/-! UNRUN handwritten model of the two staged CSEL decisions in the locked
four-limb approximation. The one-word fallback is connected to the entire
packed input when all three upper joint words are zero. Nonfallback prefix
correspondence, first-divergence progress and compiled execution remain open. -/

structure SourceFourWords where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64

structure SourceWindowRegisters where
  highA : UInt64
  highB : UInt64
  lowA : UInt64
  lowB : UInt64
  index : Nat

def sourceFirstWindowChoice (a b : SourceFourWords) : SourceWindowRegisters :=
  if (a.w3 ||| b.w3) ≠ 0 then ⟨a.w3, b.w3, a.w2, b.w2, 3⟩
  else ⟨a.w2, b.w2, a.w1, b.w1, 2⟩

def sourceSecondWindowChoice (a b : SourceFourWords) : SourceWindowRegisters :=
  let prior := sourceFirstWindowChoice a b
  if (prior.highA ||| prior.highB) ≠ 0 then prior
  else ⟨prior.lowA, prior.lowB, a.w0, b.w0, 1⟩

def sourcePackedFourWords (a : SourceFourWords) : Nat :=
  packWords [a.w0, a.w1, a.w2, a.w3]

def sourceFourWordAlignedValues (a b : SourceFourWords) : Nat × Nat :=
  let selected := sourceSecondWindowChoice a b
  let common := sourceCommonWindow selected.highA selected.highB selected.lowA selected.lowB
  ((sourceAlignedWindowWord common.highA selected.lowA common.count).toNat,
   (sourceAlignedWindowWord common.highB selected.lowB common.count).toNat)

theorem original_two_staged_choices_select_the_joint_highest_upper_window
    (a b : SourceFourWords) :
    sourceSecondWindowChoice a b =
      if (a.w3 ||| b.w3) ≠ 0 then ⟨a.w3, b.w3, a.w2, b.w2, 3⟩
      else if (a.w2 ||| b.w2) ≠ 0 then ⟨a.w2, b.w2, a.w1, b.w1, 2⟩
      else ⟨a.w1, b.w1, a.w0, b.w0, 1⟩ := by
  by_cases top : (a.w3 ||| b.w3) ≠ 0
  · simp only [sourceSecondWindowChoice, sourceFirstWindowChoice, if_pos top]
  · simp only [sourceSecondWindowChoice, sourceFirstWindowChoice, if_neg top]

theorem original_all_zero_upper_words_reduce_the_entire_packed_input_to_its_low_word
    (a : SourceFourWords) (upper1 : a.w1 = 0) (upper2 : a.w2 = 0) (upper3 : a.w3 = 0) :
    sourcePackedFourWords a = a.w0.toNat := by
  simp only [sourcePackedFourWords, packWords, upper1, upper2, upper3,
    UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]

theorem original_joint_zero_upper_windows_derive_both_entire_input_values_at_fallback
    (a b : SourceFourWords)
    (topZero : a.w3 ||| b.w3 = 0) (middleZero : a.w2 ||| b.w2 = 0)
    (lowerZero : a.w1 ||| b.w1 = 0) :
    sourceFourWordAlignedValues a b = (sourcePackedFourWords a, sourcePackedFourWords b) := by
  have top := UInt64.or_eq_zero_iff.mp topZero
  have middle := UInt64.or_eq_zero_iff.mp middleZero
  have lower := UInt64.or_eq_zero_iff.mp lowerZero
  have chosen : sourceSecondWindowChoice a b = ⟨a.w1, b.w1, a.w0, b.w0, 1⟩ := by
    rw [original_two_staged_choices_select_the_joint_highest_upper_window,
      if_neg (by intro nonzero; exact nonzero topZero),
      if_neg (by intro nonzero; exact nonzero middleZero)]
  have zeroBits : (a.w1 ||| b.w1).toBitVec = 0#64 := by
    rw [lowerZero, UInt64.toBitVec_zero]
  have zeroCount : (a.w1 ||| b.w1).toBitVec.clz.toNat = 64 := by
    have count := congrArg BitVec.toNat (BitVec.clz_eq_iff_eq_zero.mpr zeroBits)
    change (a.w1 ||| b.w1).toBitVec.clz.toNat = 64 at count
    exact count
  have fallback := original_zero_clz_fallback_returns_both_original_low_word_values
    a.w1 b.w1 a.w0 b.w0 zeroCount
  rw [sourceFourWordAlignedValues, chosen,
    original_all_zero_upper_words_reduce_the_entire_packed_input_to_its_low_word
      a lower.1 middle.1 top.1,
    original_all_zero_upper_words_reduce_the_entire_packed_input_to_its_low_word
      b lower.2 middle.2 top.2]
  exact Prod.ext fallback.1 fallback.2

set_option pp.all true in
#check @SourceFourWords
#print axioms SourceFourWords
set_option pp.all true in
#check @SourceWindowRegisters
#print axioms SourceWindowRegisters
set_option pp.all true in
#check @sourceFirstWindowChoice
#print axioms sourceFirstWindowChoice
set_option pp.all true in
#check @sourceSecondWindowChoice
#print axioms sourceSecondWindowChoice
set_option pp.all true in
#check @sourcePackedFourWords
#print axioms sourcePackedFourWords
set_option pp.all true in
#check @sourceFourWordAlignedValues
#print axioms sourceFourWordAlignedValues
set_option pp.all true in
#check @original_two_staged_choices_select_the_joint_highest_upper_window
#print axioms original_two_staged_choices_select_the_joint_highest_upper_window
set_option pp.all true in
#check @original_all_zero_upper_words_reduce_the_entire_packed_input_to_its_low_word
#print axioms original_all_zero_upper_words_reduce_the_entire_packed_input_to_its_low_word
set_option pp.all true in
#check @original_joint_zero_upper_windows_derive_both_entire_input_values_at_fallback
#print axioms original_joint_zero_upper_windows_derive_both_entire_input_values_at_fallback
end ShielddSecurity.TransferBlstArmInverseWindowSelect01
