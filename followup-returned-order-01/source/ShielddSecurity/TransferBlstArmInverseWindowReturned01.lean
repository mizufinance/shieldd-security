import ShielddSecurity.TransferBlstArmInverseWindowBfxilBridge01
import ShielddSecurity.TransferBlstArmInverseWindowError01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWindowReturned01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseWindowBfxil01 (sourceWindowLow31Word)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
attribute [local irreducible] sourceFactorWalk sourceActualFactorQuotients

/-! UNRUN handwritten final word-producing approximation model. The high
window is selected/aligned and its low31 bits are replaced by the original
low word. The exact bridge retains the existing factor recurrence and error
theorem. Compiled ISA, caller provenance and first-divergence progress are open. -/

def sourceFourWordApproximationWords (a b : SourceFourWords) : UInt64 × UInt64 :=
  let windows := sourceFourWordWindowWords a b
  (sourceWindowLow31Word windows.1 a.w0, sourceWindowLow31Word windows.2 b.w0)

theorem original_returned_approximation_words_have_the_existing_model_observations
    (a b : SourceFourWords) :
    (sourceFourWordApproximationWords a b).1.toNat =
        sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0 ∧
      (sourceFourWordApproximationWords a b).2.toNat =
        sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0 := by
  exact ⟨TransferBlstArmInverseWindowBfxilBridge01.original_typed_bfxil_word_observation_is_the_existing_low31_approximation _ _,
    TransferBlstArmInverseWindowBfxilBridge01.original_typed_bfxil_word_observation_is_the_existing_low31_approximation _ _⟩

theorem original_returned_word_producer_derives_both_entire_input_factor_prefix_error_bounds
    (count : Nat) (a b : SourceFourWords) (bounded : count ≤ 31) (oddB : b.w0.toNat % 2 = 1) :
    let approximation := sourceFourWordApproximationWords a b
    let shift := sourceFourWordWindowShift a b
    let factors := sourceFactorWalk count (sourceFactorInitial approximation.1.toNat approximation.2.toNat)
    let actual := sourceActualFactorQuotients count approximation.1.toNat approximation.2.toNat
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    (actual.1 - ((2 ^ shift : Nat) : Int) * (factors.a : Int)).natAbs ≤ 2 ^ shift * 2147483648 ∧
      (actual.2 - ((2 ^ shift : Nat) : Int) * (factors.b : Int)).natAbs ≤ 2 ^ shift * 2147483648 := by
  dsimp only
  have observations := original_returned_approximation_words_have_the_existing_model_observations a b
  rw [observations.1, observations.2]
  exact TransferBlstArmInverseWindowError01.original_source_produced_four_word_windows_derive_both_factor_prefix_error_bounds
    count a b bounded oddB

end ShielddSecurity.TransferBlstArmInverseWindowReturned01
