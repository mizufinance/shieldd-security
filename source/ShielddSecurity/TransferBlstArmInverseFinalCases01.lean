import ShielddSecurity.TransferBlstArmInverseLastingRow01
import ShielddSecurity.TransferBlstArmInverseMismatchCases01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseFinalCases01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseFirstMismatch01 (sourceFirstControlMismatch)
open TransferBlstArmInverseTraceRows01 (sourceFactorControl)

/-! UNRUN final source-model cases for the original31-step approximation.
Every original input pair with odd lowB either keeps all controls aligned
with the exact natural recurrence, or its final signed quotient pair has a
small component. A computed-shift power bound is not yet actual bitlength
progress; width identification and compiled native operations remain open. -/

theorem three_low31_error_budgets_are_strictly_below_the_shift_plus33_power
    (shift : Nat) : 3 * 2 ^ (shift + 31) < 2 ^ (shift + 33) := by
  have split : shift + 33 = (shift + 31) + 2 := by omega
  have four : (2 : Nat) ^ 2 = 4 := by decide +kernel
  calc
    _ < 4 * 2 ^ (shift + 31) := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.two_pow_pos _)
    _ = _ := by rw [split, Nat.pow_add (2 : Nat) (shift + 31) 2, four, Nat.mul_comm]

theorem original_first_mismatch_derives_a_strict_final_signed_small_component_bound
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31)
    (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approxA := sourceApproxLow31 windows.1 a.w0
    let approxB := sourceApproxLow31 windows.2 b.w0
    let approximate := sourceFactorInitial approxA approxB
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    let final := sourceActualFactorQuotients 31 approxA approxB
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    sourceFirstControlMismatch count approximate actual →
      min final.1.natAbs final.2.natAbs < 2 ^ (sourceFourWordWindowShift a b + 33) := by
  dsimp only
  intro first
  have sum : count + 1 + (31 - (count + 1)) = 31 := by omega
  have bound := TransferBlstArmInverseLastingRow01.original_first_mismatch_preserves_a_small_signed_quotient_component_through_prefix31
    count (31 - (count + 1)) a b bounded (by omega) oddB first
  rw [sum] at bound
  exact Nat.lt_of_le_of_lt bound
    (three_low31_error_budgets_are_strictly_below_the_shift_plus33_power _)

theorem original31_controls_derive_exact_final_alignment_or_a_strict_small_signed_component
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approxA := sourceApproxLow31 windows.1 a.w0
    let approxB := sourceApproxLow31 windows.2 b.w0
    let approximate := sourceFactorInitial approxA approxB
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    let final := sourceActualFactorQuotients 31 approxA approxB
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    ((∀ index < 31, sourceFactorControl (sourceFactorWalk index approximate) =
        sourceFactorControl (sourceFactorWalk index actual)) ∧
      final = (((sourceFactorWalk 31 actual).a : Int), ((sourceFactorWalk 31 actual).b : Int))) ∨
      min final.1.natAbs final.2.natAbs < 2 ^ (sourceFourWordWindowShift a b + 33) := by
  dsimp only
  have cases := TransferBlstArmInverseMismatchCases01.original_source_31_controls_derive_final_alignment_or_a_bounded_first_mismatch
    a b oddB
  rcases cases with synchronized | ⟨count, bounded, first, _⟩
  · exact Or.inl synchronized
  · exact Or.inr (original_first_mismatch_derives_a_strict_final_signed_small_component_bound
      count a b bounded oddB first)

set_option pp.all true in
#check @three_low31_error_budgets_are_strictly_below_the_shift_plus33_power
#print axioms three_low31_error_budgets_are_strictly_below_the_shift_plus33_power
set_option pp.all true in
#check @original_first_mismatch_derives_a_strict_final_signed_small_component_bound
#print axioms original_first_mismatch_derives_a_strict_final_signed_small_component_bound
set_option pp.all true in
#check @original31_controls_derive_exact_final_alignment_or_a_strict_small_signed_component
#print axioms original31_controls_derive_exact_final_alignment_or_a_strict_small_signed_component
end ShielddSecurity.TransferBlstArmInverseFinalCases01
