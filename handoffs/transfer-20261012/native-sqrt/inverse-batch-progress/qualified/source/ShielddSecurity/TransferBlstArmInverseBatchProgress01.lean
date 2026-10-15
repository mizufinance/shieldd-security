import ShielddSecurity.TransferBlstArmInverseNaturalProgress01
import ShielddSecurity.TransferBlstArmInverseMismatchCases01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseBatchProgress01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseBitlengthBudget01 (sourceNatBitlength)

/-! Exhaustive source batch progress: every original31-step approximation
either reaches an exact zero first full output or reduces the sum of the
two full magnitude bitlengths by at least31. Source control partition and
producer observations derive every premise. Native word execution, GCD
preservation, final47-step schedule and complete inversion remain open. -/

theorem every_original_four_word31_step_batch_reaches_zero_or_decreases_pair_bitlength_by31
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    let final := sourceActualFactorQuotients 31
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    final.1 = 0 ∨
      sourceNatBitlength final.1.natAbs + sourceNatBitlength final.2.natAbs + 31 ≤
        sourceNatBitlength (sourcePackedFourWords a) + sourceNatBitlength (sourcePackedFourWords b) := by
  dsimp only
  have cases := TransferBlstArmInverseMismatchCases01.original_source_31_controls_derive_final_alignment_or_a_bounded_first_mismatch a b oddB
  dsimp only at cases
  rcases cases with synchronized | ⟨count, bounded, first, _gap⟩
  · rw [synchronized.2]
    have progress := TransferBlstArmInverseNaturalProgress01.every_original_natural_factor_walk_reaches_zero_or_decreases_by_its_length
      31 (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))
    rcases progress with terminal | decreases
    · left
      rw [terminal]
      rfl
    · right
      exact decreases
  · right
    exact TransferBlstArmInverseMismatchProgress01.original_first_control_mismatch_decreases_the_full_pair_bitlength_by_at_least31
      count a b bounded oddB first

set_option pp.all true in
#check @every_original_four_word31_step_batch_reaches_zero_or_decreases_pair_bitlength_by31
#print axioms every_original_four_word31_step_batch_reaches_zero_or_decreases_pair_bitlength_by31
end ShielddSecurity.TransferBlstArmInverseBatchProgress01
