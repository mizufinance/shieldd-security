import ShielddSecurity.TransferBlstArmInverseTraceRows01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseFirstMismatch01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseTraceRows01 (sourceFactorControl)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)

/-! UNRUN conditional first control-mismatch candidate in two exact source
recurrences. All earlier controls must agree; parity at the candidate remains
explicit. That prefix derives natural/signed alignment before applying the
producer error bound. No mismatch existence, actual ISA trace or progress. -/

def sourceFirstControlMismatch (count : Nat) (approximate actual : SourceFactors) : Prop :=
  (∀ index < count,
    sourceFactorControl (sourceFactorWalk index approximate) =
      sourceFactorControl (sourceFactorWalk index actual)) ∧
  sourceFactorControl (sourceFactorWalk count approximate) ≠
    sourceFactorControl (sourceFactorWalk count actual)

theorem original_odd_low_word_derives_odd_entire_four_word_input
    (b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    sourcePackedFourWords b % 2 = 1 := by
  change (b.w0.toNat + TransferScalarSerializationRange01.radix64 *
    TransferScalarWordPrimitives01.packWords [b.w1, b.w2, b.w3]) % 2 = 1
  have radixEven : TransferScalarSerializationRange01.radix64 % 2 = 0 := by decide +kernel
  have tailEven : (TransferScalarSerializationRange01.radix64 *
      TransferScalarWordPrimitives01.packWords [b.w1, b.w2, b.w3]) % 2 = 0 := by
    rw [Nat.mul_mod, radixEven, Nat.zero_mul, Nat.zero_mod]
  rw [Nat.add_mod, tailEven, Nat.add_zero, Nat.mod_mod]
  exact oddB

theorem original_source_first_control_mismatch_with_matched_parity_derives_the_exact_loop_gap
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approximate := sourceFactorInitial
      (sourceApproxLow31 windows.1 a.w0) (sourceApproxLow31 windows.2 b.w0)
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    sourceFirstControlMismatch count approximate actual →
    (sourceFactorWalk count actual).a % 2 = (sourceFactorWalk count approximate).a % 2 →
    (((sourceFactorWalk count actual).a : Int) - ((sourceFactorWalk count actual).b : Int)).natAbs ≤
      2 ^ (sourceFourWordWindowShift a b + 32) := by
  dsimp only
  intro first parity
  have alignment := TransferBlstArmInverseTraceRows01.synchronized_initialized_prefix_identifies_both_signed_actual_quotients
    count (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
    (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
    (sourcePackedFourWords a) (sourcePackedFourWords b)
    (original_odd_low_word_derives_odd_entire_four_word_input b oddB) first.1
  have disagreement := TransferBlstArmInverseTraceRows01.matched_parity_and_different_controls_derive_strict_signed_comparison_disagreement
    (sourceFactorWalk count (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)))
    (sourceFactorWalk count (sourceFactorInitial
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))) parity (Ne.symm first.2)
  have signedDisagreement : TransferBlstArmInverseOrderStep01.sourceComparisonDisagreement
      (sourceActualFactorQuotients count
        (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
        (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)).1
      (sourceActualFactorQuotients count
        (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
        (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)).2
      (sourceFactorWalk count (sourceFactorInitial
        (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))).a
      (sourceFactorWalk count (sourceFactorInitial
        (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))).b := by
    rw [alignment]
    exact disagreement
  have gap := TransferBlstArmInverseOrderStep01.strict_source_prefix_comparison_disagreement_derives_the_entire_signed_gap_bound
    count a b bounded oddB signedDisagreement
  dsimp only at gap
  rw [alignment] at gap
  exact gap

end ShielddSecurity.TransferBlstArmInverseFirstMismatch01
