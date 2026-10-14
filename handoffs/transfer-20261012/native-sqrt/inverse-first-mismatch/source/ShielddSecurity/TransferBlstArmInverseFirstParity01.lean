import ShielddSecurity.TransferBlstArmInversePrefixParity01
import ShielddSecurity.TransferBlstArmInverseFirstMismatch01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseFirstParity01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseFirstMismatch01 (sourceFirstControlMismatch)
open TransferBlstArmInverseTraceRows01 (sourceFactorControl)

/-! UNRUN removal of the explicit candidate-parity premise from the conditional
first control-mismatch bound. Earlier source controls derive signed/natural
alignment; original low31 lifts derive parity strictly below count31. First
mismatch existence, actual native trace, lasting behavior and progress are open. -/

theorem original_inputs_and_earlier_control_synchronization_derive_both_natural_loop_parities
    (count : Nat) (highA highB : UInt64) (a b : SourceFourWords)
    (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1) :
    let approximate := sourceFactorInitial (sourceApproxLow31 highA a.w0) (sourceApproxLow31 highB b.w0)
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    (∀ index < count, sourceFactorControl (sourceFactorWalk index approximate) =
      sourceFactorControl (sourceFactorWalk index actual)) →
    (sourceFactorWalk count actual).a % 2 = (sourceFactorWalk count approximate).a % 2 ∧
      (sourceFactorWalk count actual).b % 2 = (sourceFactorWalk count approximate).b % 2 := by
  dsimp only
  intro synchronized
  have parities := TransferBlstArmInversePrefixParity01.original_four_word_inputs_derive_both_signed_prefix_quotient_parities
    count highA highB a b bounded oddB
  dsimp only at parities
  have alignment := TransferBlstArmInverseTraceRows01.synchronized_initialized_prefix_identifies_both_signed_actual_quotients
    count (sourceApproxLow31 highA a.w0) (sourceApproxLow31 highB b.w0)
    (sourcePackedFourWords a) (sourcePackedFourWords b)
    (TransferBlstArmInverseFirstMismatch01.original_odd_low_word_derives_odd_entire_four_word_input b oddB) synchronized
  rw [alignment] at parities
  have left := parities.1
  have right := parities.2
  constructor <;> omega

theorem original_source_first_control_mismatch_derives_the_exact_loop_gap_without_a_parity_premise
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approximate := sourceFactorInitial
      (sourceApproxLow31 windows.1 a.w0) (sourceApproxLow31 windows.2 b.w0)
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    sourceFirstControlMismatch count approximate actual →
    (((sourceFactorWalk count actual).a : Int) - ((sourceFactorWalk count actual).b : Int)).natAbs ≤
      2 ^ (sourceFourWordWindowShift a b + 32) := by
  dsimp only
  intro first
  have parity := original_inputs_and_earlier_control_synchronization_derive_both_natural_loop_parities
    count (sourceFourWordWindowWords a b).1 (sourceFourWordWindowWords a b).2 a b bounded oddB first.1
  exact TransferBlstArmInverseFirstMismatch01.original_source_first_control_mismatch_with_matched_parity_derives_the_exact_loop_gap
    count a b bounded oddB first parity.1

set_option pp.all true in
#check @original_inputs_and_earlier_control_synchronization_derive_both_natural_loop_parities
#print axioms original_inputs_and_earlier_control_synchronization_derive_both_natural_loop_parities
set_option pp.all true in
#check @original_source_first_control_mismatch_derives_the_exact_loop_gap_without_a_parity_premise
#print axioms original_source_first_control_mismatch_derives_the_exact_loop_gap_without_a_parity_premise
end ShielddSecurity.TransferBlstArmInverseFirstParity01
