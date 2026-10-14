import ShielddSecurity.TransferBlstArmInverseFirstParity01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseMismatchCases01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseTraceRows01 (sourceFactorControl)
open TransferBlstArmInverseFirstMismatch01 (sourceFirstControlMismatch)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)

/-! UNRUN exhaustive finite source control cases. A mismatch need not exist:
either every earlier control matches or a first candidate exists. Original
low31 premises derive its gap bound; all31 matching controls derive final
signed/natural alignment. Neither branch establishes31-bit batch progress,
native loop/ISA correspondence or actual signed word multiplication. -/

theorem finite_source_control_prefixes_partition_into_agreement_or_a_first_mismatch
    (limit : Nat) (approximate actual : SourceFactors) :
    (∀ index < limit, sourceFactorControl (sourceFactorWalk index approximate) =
      sourceFactorControl (sourceFactorWalk index actual)) ∨
    ∃ count < limit, sourceFirstControlMismatch count approximate actual := by
  induction limit with
  | zero =>
      left
      intro index less
      omega
  | succ limit ih =>
      rcases ih with synchronized | ⟨count, less, first⟩
      · by_cases last : sourceFactorControl (sourceFactorWalk limit approximate) =
            sourceFactorControl (sourceFactorWalk limit actual)
        · left
          intro index less
          by_cases earlier : index < limit
          · exact synchronized index earlier
          · have sameIndex : index = limit := by omega
            subst index
            exact last
        · right
          exact ⟨limit, Nat.lt_succ_self limit, ⟨synchronized, last⟩⟩
      · right
        exact ⟨count, Nat.lt_trans less (Nat.lt_succ_self limit), first⟩

theorem original_source_31_controls_derive_final_alignment_or_a_bounded_first_mismatch
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approxA := sourceApproxLow31 windows.1 a.w0
    let approxB := sourceApproxLow31 windows.2 b.w0
    let approximate := sourceFactorInitial approxA approxB
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    ((∀ index < 31, sourceFactorControl (sourceFactorWalk index approximate) =
        sourceFactorControl (sourceFactorWalk index actual)) ∧
      sourceActualFactorQuotients 31 approxA approxB
        (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int) =
        (((sourceFactorWalk 31 actual).a : Int), ((sourceFactorWalk 31 actual).b : Int))) ∨
    ∃ count < 31, sourceFirstControlMismatch count approximate actual ∧
      (((sourceFactorWalk count actual).a : Int) - ((sourceFactorWalk count actual).b : Int)).natAbs ≤
        2 ^ (sourceFourWordWindowShift a b + 32) := by
  dsimp only
  have partition := finite_source_control_prefixes_partition_into_agreement_or_a_first_mismatch 31
    (sourceFactorInitial (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))
    (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))
  rcases partition with synchronized | ⟨count, bounded, first⟩
  · left
    exact ⟨synchronized,
      TransferBlstArmInverseTraceRows01.synchronized_initialized_prefix_identifies_both_signed_actual_quotients
        31 (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
        (sourcePackedFourWords a) (sourcePackedFourWords b)
        (TransferBlstArmInverseFirstMismatch01.original_odd_low_word_derives_odd_entire_four_word_input b oddB)
        synchronized⟩
  · right
    exact ⟨count, bounded, first,
      TransferBlstArmInverseFirstParity01.original_source_first_control_mismatch_derives_the_exact_loop_gap_without_a_parity_premise
        count a b bounded oddB first⟩

set_option pp.all true in
#check @finite_source_control_prefixes_partition_into_agreement_or_a_first_mismatch
#print axioms finite_source_control_prefixes_partition_into_agreement_or_a_first_mismatch
set_option pp.all true in
#check @original_source_31_controls_derive_final_alignment_or_a_bounded_first_mismatch
#print axioms original_source_31_controls_derive_final_alignment_or_a_bounded_first_mismatch
end ShielddSecurity.TransferBlstArmInverseMismatchCases01
