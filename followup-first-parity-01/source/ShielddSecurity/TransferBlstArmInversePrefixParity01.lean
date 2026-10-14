import Init.Data.Int.Lemmas
import Init.Data.Int.Pow
import Lean.Elab.Tactic.Omega
import ShielddSecurity.TransferBlstArmInversePrefixDiv01
import ShielddSecurity.TransferBlstArmInverseErrorRows01
import ShielddSecurity.TransferBlstArmInverseWindowSelect01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePrefixParity01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)

/-! UNRUN parity of original source-controlled signed quotients strictly below
prefix31. One extra radix bit in each full-input lift yields an even quotient
correction. Uses symbolic rows and core integer distributivity, not Ring or
unrolled constraints. No sign, native trace or progress inferred from parity. -/

theorem two_even_radix_input_lifts_and_tracked_row_derive_the_exact_quotient_parity
    (radix inputA inputB approxA approxB deltaA deltaB f g value : Int)
    (nonzero : radix ≠ 0)
    (leftLift : inputA = approxA + radix * (2 * deltaA))
    (rightLift : inputB = approxB + radix * (2 * deltaB))
    (tracked : radix * value = f * approxA + g * approxB) :
    ((f * inputA + g * inputB) / radix) % 2 = value % 2 := by
  have leftProduct : f * (radix * (2 * deltaA)) = radix * (2 * (f * deltaA)) := by
    calc
      _ = radix * (f * (2 * deltaA)) := Int.mul_left_comm _ _ _
      _ = _ := congrArg (fun x : Int => radix * x) (Int.mul_left_comm _ _ _)
  have rightProduct : g * (radix * (2 * deltaB)) = radix * (2 * (g * deltaB)) := by
    calc
      _ = radix * (g * (2 * deltaB)) := Int.mul_left_comm _ _ _
      _ = _ := congrArg (fun x : Int => radix * x) (Int.mul_left_comm _ _ _)
  have distribute : radix * (2 * (f * deltaA + g * deltaB)) =
      radix * (2 * (f * deltaA)) + radix * (2 * (g * deltaB)) := by
    rw [Int.mul_add, Int.mul_add]
  have numerator : f * inputA + g * inputB =
      radix * (value + 2 * (f * deltaA + g * deltaB)) := by
    calc
      _ = (f * approxA + radix * (2 * (f * deltaA))) +
          (g * approxB + radix * (2 * (g * deltaB))) := by
        rw [leftLift, rightLift, Int.mul_add, Int.mul_add, leftProduct, rightProduct]
      _ = (f * approxA + g * approxB) + radix * (2 * (f * deltaA + g * deltaB)) := by
        rw [distribute]
        omega
      _ = radix * value + radix * (2 * (f * deltaA + g * deltaB)) := by rw [tracked]
      _ = _ := (Int.mul_add _ _ _).symm
  rw [numerator, Int.mul_ediv_cancel_left _ nonzero]
  omega

theorem original_low31_input_lift_strictly_before_prefix31_has_an_even_prefix_correction
    (count approx : Nat) (input delta : Int) (bounded : count < 31)
    (lifted : input = (approx : Int) + 2147483648 * delta) :
    ∃ prefixDelta : Int, input = (approx : Int) + (2 : Int) ^ count * (2 * prefixDelta) := by
  have nextBound : count + 1 ≤ 31 := by omega
  rcases TransferBlstArmInversePrefixDiv01.original_full_low31_input_lift_derives_an_exact_lift_for_every_prefix
    (count + 1) approx input delta nextBound lifted with ⟨prefixDelta, nextLift⟩
  refine ⟨prefixDelta, ?_⟩
  rw [nextLift, Int.pow_succ, Int.mul_assoc]

theorem original_four_word_inputs_derive_both_signed_prefix_quotient_parities
    (count : Nat) (highA highB : UInt64) (a b : SourceFourWords)
    (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1) :
    let approxA := sourceApproxLow31 highA a.w0
    let approxB := sourceApproxLow31 highB b.w0
    let factors := sourceFactorWalk count (sourceFactorInitial approxA approxB)
    let actual := sourceActualFactorQuotients count approxA approxB
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    actual.1 % 2 = (factors.a : Int) % 2 ∧ actual.2 % 2 = (factors.b : Int) % 2 := by
  dsimp only
  rcases TransferBlstArmInverseApproxInput01.original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference
    highA a.w0 [a.w1, a.w2, a.w3] with ⟨deltaA, inputA⟩
  rcases TransferBlstArmInverseApproxInput01.original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference
    highB b.w0 [b.w1, b.w2, b.w3] with ⟨deltaB, inputB⟩
  change (sourcePackedFourWords a : Int) = (sourceApproxLow31 highA a.w0 : Int) + 2147483648 * deltaA at inputA
  change (sourcePackedFourWords b : Int) = (sourceApproxLow31 highB b.w0 : Int) + 2147483648 * deltaB at inputB
  rcases original_low31_input_lift_strictly_before_prefix31_has_an_even_prefix_correction count
    (sourceApproxLow31 highA a.w0) (sourcePackedFourWords a : Int) deltaA bounded inputA with ⟨liftA, leftLift⟩
  rcases original_low31_input_lift_strictly_before_prefix31_has_an_even_prefix_correction count
    (sourceApproxLow31 highB b.w0) (sourcePackedFourWords b : Int) deltaB bounded inputB with ⟨liftB, rightLift⟩
  let factors := sourceFactorWalk count (sourceFactorInitial
    (sourceApproxLow31 highA a.w0) (sourceApproxLow31 highB b.w0))
  have tracked := TransferBlstArmInverseFactors01.original_initialized_factor_walk_derives_exact_scaled_input_rows
    count (sourceApproxLow31 highA a.w0) (sourceApproxLow31 highB b.w0)
    (TransferBlstArmInverseApproxBits01.original_low31_approximation_preserves_oddness_of_the_original_low_word highB b.w0 oddB)
  change (2 : Int) ^ count * (factors.a : Int) =
      factors.f0 * (sourceApproxLow31 highA a.w0 : Int) + factors.g0 * (sourceApproxLow31 highB b.w0 : Int) ∧
    (2 : Int) ^ count * (factors.b : Int) =
      factors.f1 * (sourceApproxLow31 highA a.w0 : Int) + factors.g1 * (sourceApproxLow31 highB b.w0 : Int) at tracked
  have nonzero : (2 : Int) ^ count ≠ 0 := Int.pow_ne_zero (by decide)
  change ((factors.f0 * (sourcePackedFourWords a : Int) + factors.g0 * (sourcePackedFourWords b : Int)) / (2 : Int) ^ count) % 2 =
      (factors.a : Int) % 2 ∧
    ((factors.f1 * (sourcePackedFourWords a : Int) + factors.g1 * (sourcePackedFourWords b : Int)) / (2 : Int) ^ count) % 2 =
      (factors.b : Int) % 2
  exact ⟨two_even_radix_input_lifts_and_tracked_row_derive_the_exact_quotient_parity
    _ _ _ _ _ liftA liftB _ _ _ nonzero leftLift rightLift tracked.1,
    two_even_radix_input_lifts_and_tracked_row_derive_the_exact_quotient_parity
    _ _ _ _ _ liftA liftB _ _ _ nonzero leftLift rightLift tracked.2⟩

end ShielddSecurity.TransferBlstArmInversePrefixParity01
