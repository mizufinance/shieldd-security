import ShielddSecurity.TransferBlstArmInverseWindowInput01
import ShielddSecurity.TransferBlstArmInversePrefixError01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowError01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
attribute [local irreducible] sourceFactorWalk sourceActualFactorQuotients

/-! UNRUN handwritten source-producer join. The whole-input high-window
premises of PrefixError are discharged by the modeled staged load/CSEL/CLZ
and word alignment, including one-word fallback. Count and original low-word
oddness remain explicit domain premises. First-divergence/bitlength progress,
actual signed multiply/carry/shift and compiled native execution remain open. -/

theorem original_source_produced_four_word_windows_derive_both_factor_prefix_error_bounds
    (count : Nat) (a b : SourceFourWords) (bounded : count ≤ 31) (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let shift := sourceFourWordWindowShift a b
    let factors := sourceFactorWalk count (sourceFactorInitial
      (sourceApproxLow31 windows.1 a.w0) (sourceApproxLow31 windows.2 b.w0))
    let actual := sourceActualFactorQuotients count
      (sourceApproxLow31 windows.1 a.w0) (sourceApproxLow31 windows.2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    (actual.1 - ((2 ^ shift : Nat) : Int) * (factors.a : Int)).natAbs ≤ 2 ^ shift * 2147483648 ∧
      (actual.2 - ((2 ^ shift : Nat) : Int) * (factors.b : Int)).natAbs ≤ 2 ^ shift * 2147483648 := by
  have windows := TransferBlstArmInverseWindowInput01.original_source_window_words_derive_the_high_window_premises_for_both_entire_inputs a b
  exact TransferBlstArmInversePrefixError01.original_entire_input_factor_prefixes_preserve_both_initial_window_error_bounds
    count (sourceFourWordWindowShift a b)
    (sourceFourWordWindowWords a b).1 a.w0 (sourceFourWordWindowWords a b).2 b.w0
    [a.w1, a.w2, a.w3] [b.w1, b.w2, b.w3] bounded oddB windows.1 windows.2

set_option pp.all true in
#check @original_source_produced_four_word_windows_derive_both_factor_prefix_error_bounds
#print axioms original_source_produced_four_word_windows_derive_both_factor_prefix_error_bounds
end ShielddSecurity.TransferBlstArmInverseWindowError01
