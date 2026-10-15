import ShielddSecurity.TransferBlstArmInverseRowCompose01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseProducedRows01
open TransferBlstArmInverseRowCompose01 (SourceLinearRows SourceLinearTracks)
open TransferBlstArmInverseWordRepack01 (sourceFourWordsOfNat)
open TransferBlstArmInverseWindowSelect01 (sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseMagnitudeRows01 (sourceMagnitudeSign)
open TransferBlstArmInverseMagnitudeBatch01 (sourceMagnitudeBatch)

/-! Original-window production of sign-corrected full coefficient rows for
repacked source batches. Every row comes from the initialized source factor
walk and its exact full quotient, rather than a supplied row observation.
Native coefficient decoding and compiled word operations remain open. -/

def sourcePrefixMagnitudes (count : Nat) (input : Nat × Nat) : Nat × Nat :=
  let a := sourceFourWordsOfNat input.1
  let b := sourceFourWordsOfNat input.2
  let actual := sourceActualFactorQuotients count
    (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
    (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
    (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
  (actual.1.natAbs, actual.2.natAbs)

def sourcePrefixLinearRows (count : Nat) (input : Nat × Nat) : SourceLinearRows :=
  let a := sourceFourWordsOfNat input.1
  let b := sourceFourWordsOfNat input.2
  let approxA := sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0
  let approxB := sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0
  let factors := sourceFactorWalk count (sourceFactorInitial approxA approxB)
  let actual := sourceActualFactorQuotients count approxA approxB
    (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
  ⟨sourceMagnitudeSign actual.1 * factors.f0, sourceMagnitudeSign actual.1 * factors.g0,
   sourceMagnitudeSign actual.2 * factors.f1, sourceMagnitudeSign actual.2 * factors.g1⟩

theorem original_repacked_prefix_produces_rows_tracking_both_entire_magnitudes
    (count : Nat) (input : Nat × Nat) (bounded : count ≤ 31)
    (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256) (odd : input.2 % 2 = 1) :
    SourceLinearTracks (input.1 : Int) (input.2 : Int) ((2 : Int) ^ count)
      ((sourcePrefixMagnitudes count input).1 : Int) ((sourcePrefixMagnitudes count input).2 : Int)
      (sourcePrefixLinearRows count input) := by
  have actual := TransferBlstArmInverseMagnitudeRows01.original_full_input_prefixes_derive_both_exact_sign_corrected_magnitude_rows
    count (sourceFourWordsOfNat input.1) (sourceFourWordsOfNat input.2) bounded
    (TransferBlstArmInverseWordRepack01.an_odd_natural_input_has_an_odd_original_repacked_low_word input.2 odd)
  have left := TransferBlstArmInverseWordRepack01.original_four_word_repacking_reconstructs_every_input_below_two256 input.1 leftBound
  have right := TransferBlstArmInverseWordRepack01.original_four_word_repacking_reconstructs_every_input_below_two256 input.2 rightBound
  dsimp only at actual
  dsimp only [sourcePrefixMagnitudes, sourcePrefixLinearRows, SourceLinearTracks]
  rw [left, right] at actual ⊢
  exact actual

theorem original_magnitude_batch_produces_its_exact_full_sign_corrected_rows
    (input : Nat × Nat) (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256)
    (odd : input.2 % 2 = 1) :
    SourceLinearTracks (input.1 : Int) (input.2 : Int) ((2 : Int) ^ 31)
      ((sourceMagnitudeBatch input).1 : Int) ((sourceMagnitudeBatch input).2 : Int)
      (sourcePrefixLinearRows 31 input) := by
  exact original_repacked_prefix_produces_rows_tracking_both_entire_magnitudes 31 input (Nat.le_refl _) leftBound rightBound odd

set_option pp.all true in
#check @sourcePrefixMagnitudes
#print axioms sourcePrefixMagnitudes
set_option pp.all true in
#check @sourcePrefixLinearRows
#print axioms sourcePrefixLinearRows
set_option pp.all true in
#check @original_repacked_prefix_produces_rows_tracking_both_entire_magnitudes
#print axioms original_repacked_prefix_produces_rows_tracking_both_entire_magnitudes
set_option pp.all true in
#check @original_magnitude_batch_produces_its_exact_full_sign_corrected_rows
#print axioms original_magnitude_batch_produces_its_exact_full_sign_corrected_rows
end ShielddSecurity.TransferBlstArmInverseProducedRows01
