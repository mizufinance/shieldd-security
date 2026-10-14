import ShielddSecurity.TransferBlstArmInverseWindowPrefix01
import ShielddSecurity.TransferBlstArmInverseWindowJoint01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowInput01
open TransferBlstArmInverseWindowSelect01
open TransferBlstArmInverseWindowPrefix01
open TransferBlstArmInverseWindowJoint01
open TransferBlstArmInverseWindowClz01
open TransferBlstArmInverseWindowAlign01
open TransferScalarSerializationRange01 (radix64)

/-! UNRUN handwritten producer composition. The window denominator and shift
are computed from the staged joint selection and CLZ, including fallback.
Whole-input quotient observations are derived from all four original words.
Runtime width/bitlength progress, native loads/ISA and full inversion remain open. -/

def sourceFourWordWindowDivisor (a b : SourceFourWords) : Nat :=
  let selected := sourceSecondWindowChoice a b
  let common := sourceCommonWindow selected.highA selected.highB selected.lowA selected.lowB
  if selected.highA ||| selected.highB = 0 then 1
  else radix64 ^ (selected.index - 1) * 2 ^ (64 - common.count)

def sourceFourWordWindowShift (a b : SourceFourWords) : Nat :=
  let selected := sourceSecondWindowChoice a b
  let common := sourceCommonWindow selected.highA selected.highB selected.lowA selected.lowB
  if selected.highA ||| selected.highB = 0 then 0
  else 64 * (selected.index - 1) + (64 - common.count)

def sourceFourWordWindowWords (a b : SourceFourWords) : UInt64 × UInt64 :=
  let selected := sourceSecondWindowChoice a b
  let common := sourceCommonWindow selected.highA selected.highB selected.lowA selected.lowB
  (sourceAlignedWindowWord common.highA selected.lowA common.count,
   sourceAlignedWindowWord common.highB selected.lowB common.count)

theorem original_source_computed_window_divisor_is_the_exact_shift_power
    (a b : SourceFourWords) : sourceFourWordWindowDivisor a b = 2 ^ sourceFourWordWindowShift a b := by
  dsimp only [sourceFourWordWindowDivisor, sourceFourWordWindowShift]
  by_cases zero : (sourceSecondWindowChoice a b).highA ||| (sourceSecondWindowChoice a b).highB = 0
  · simp only [if_pos zero, pow_zero]
  · rw [if_neg zero, radix64, ← Nat.pow_mul, ← Nat.pow_add]

theorem original_staged_four_word_window_derives_both_entire_input_quotients
    (a b : SourceFourWords) :
    sourceFourWordAlignedValues a b =
      (sourcePackedFourWords a / sourceFourWordWindowDivisor a b,
       sourcePackedFourWords b / sourceFourWordWindowDivisor a b) := by
  let selected := sourceSecondWindowChoice a b
  let common := sourceCommonWindow selected.highA selected.highB selected.lowA selected.lowB
  let base := radix64 ^ (selected.index - 1)
  by_cases zero : selected.highA ||| selected.highB = 0
  · have all := (original_selected_joint_window_is_zero_exactly_when_all_original_upper_joint_words_are_zero a b).mp zero
    have fallback := original_joint_zero_upper_windows_derive_both_entire_input_values_at_fallback
      a b all.1 all.2.1 all.2.2
    simpa only [sourceFourWordWindowDivisor, if_pos zero, Nat.div_one] using fallback
  · have retained := original_nonzero_joint_high_window_retains_the_selected_high_words_and_raw_clz
      selected.highA selected.highB selected.lowA selected.lowB zero
    have bounds := original_common_clz_window_derives_both_high_bounds_and_a_bounded_count
      selected.highA selected.highB selected.lowA selected.lowB
    rw [retained] at bounds
    have decomposition := original_staged_selection_derives_both_entire_input_prefixes_and_tail_bounds a b
    have basePositive : 0 < base := (Nat.pow_pos_iff).2 (Or.inl (Nat.two_pow_pos 64))
    have left := original_aligned_window_word_matches_the_whole_input_quotient_from_an_explicit_prefix
      selected.highA selected.lowA (selected.highA ||| selected.highB).toBitVec.clz.toNat
      base (sourceSelectedLowerTail a selected.index) (sourcePackedFourWords a)
      bounds.1 bounds.2.1 basePositive decomposition.2.2.1 decomposition.1
    have right := original_aligned_window_word_matches_the_whole_input_quotient_from_an_explicit_prefix
      selected.highB selected.lowB (selected.highA ||| selected.highB).toBitVec.clz.toNat
      base (sourceSelectedLowerTail b selected.index) (sourcePackedFourWords b)
      bounds.1 bounds.2.2 basePositive decomposition.2.2.2 decomposition.2.1
    change ((sourceAlignedWindowWord common.highA selected.lowA common.count).toNat,
      (sourceAlignedWindowWord common.highB selected.lowB common.count).toNat) =
      (sourcePackedFourWords a / (if selected.highA ||| selected.highB = 0 then 1 else base * 2 ^ (64 - common.count)),
       sourcePackedFourWords b / (if selected.highA ||| selected.highB = 0 then 1 else base * 2 ^ (64 - common.count)))
    rw [if_neg zero]
    dsimp only [common]
    rw [retained]
    exact Prod.ext left right

theorem original_source_window_words_derive_the_high_window_premises_for_both_entire_inputs
    (a b : SourceFourWords) :
    (sourceFourWordWindowWords a b).1.toNat = sourcePackedFourWords a / 2 ^ sourceFourWordWindowShift a b ∧
      (sourceFourWordWindowWords a b).2.toNat = sourcePackedFourWords b / 2 ^ sourceFourWordWindowShift a b := by
  have whole := original_staged_four_word_window_derives_both_entire_input_quotients a b
  rw [original_source_computed_window_divisor_is_the_exact_shift_power] at whole
  have left := congrArg (fun value : Nat × Nat => value.1) whole
  have right := congrArg (fun value : Nat × Nat => value.2) whole
  exact ⟨left, right⟩

end ShielddSecurity.TransferBlstArmInverseWindowInput01
