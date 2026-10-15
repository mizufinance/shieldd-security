import ShielddSecurity.TransferBlstArmInverseScheduleUnit01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseMagnitudeRows01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)

/-! Exact sign-corrected full rows behind source magnitude outputs. Full
input divisibility is derived from original word/low31 lifts. No selected
quotient or sign observation is supplied. Native carry/sign extraction and
extended coefficient composition remain separate obligations. -/

def sourceMagnitudeSign (value : Int) : Int := if value < 0 then -1 else 1

theorem source_magnitude_sign_times_its_value_is_the_exact_natural_magnitude
    (value : Int) : sourceMagnitudeSign value * value = (value.natAbs : Int) := by
  unfold sourceMagnitudeSign
  by_cases negative : value < 0
  · rw [if_pos negative, Int.neg_one_mul]
    have absolute := Int.eq_neg_natAbs_of_nonpos (show value ≤ 0 by omega)
    omega
  · rw [if_neg negative, Int.one_mul]
    exact Int.eq_natAbs_of_nonneg (by omega)

theorem an_exact_scaled_signed_row_derives_the_exact_sign_corrected_magnitude_row
    (scale value f g inputA inputB : Int)
    (row : scale * value = f * inputA + g * inputB) :
    scale * (value.natAbs : Int) =
      (sourceMagnitudeSign value * f) * inputA + (sourceMagnitudeSign value * g) * inputB := by
  have magnitude := source_magnitude_sign_times_its_value_is_the_exact_natural_magnitude value
  calc
    _ = sourceMagnitudeSign value * (scale * value) := by
      rw [←magnitude, Int.mul_left_comm]
    _ = sourceMagnitudeSign value * (f * inputA + g * inputB) := congrArg (fun x : Int => sourceMagnitudeSign value * x) row
    _ = _ := by rw [Int.mul_add, ←Int.mul_assoc, ←Int.mul_assoc]

theorem original_full_input_prefixes_derive_both_exact_sign_corrected_magnitude_rows
    (count : Nat) (a b : SourceFourWords) (bounded : count ≤ 31) (oddB : b.w0.toNat % 2 = 1) :
    let approxA := sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0
    let approxB := sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0
    let factors := sourceFactorWalk count (sourceFactorInitial approxA approxB)
    let actual := sourceActualFactorQuotients count approxA approxB
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    (2 : Int) ^ count * (actual.1.natAbs : Int) =
      (sourceMagnitudeSign actual.1 * factors.f0) * (sourcePackedFourWords a : Int) +
        (sourceMagnitudeSign actual.1 * factors.g0) * (sourcePackedFourWords b : Int) ∧
    (2 : Int) ^ count * (actual.2.natAbs : Int) =
      (sourceMagnitudeSign actual.2 * factors.f1) * (sourcePackedFourWords a : Int) +
        (sourceMagnitudeSign actual.2 * factors.g1) * (sourcePackedFourWords b : Int) := by
  dsimp only
  let approxA := sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0
  let approxB := sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0
  let factors := sourceFactorWalk count (sourceFactorInitial approxA approxB)
  let actual := sourceActualFactorQuotients count approxA approxB
    (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
  have divisible := TransferBlstArmInversePrefixDiv01.original_initialized_factor_prefixes_divide_both_entire_input_rows
    count (sourceFourWordWindowWords a b).1 a.w0 (sourceFourWordWindowWords a b).2 b.w0
    [a.w1, a.w2, a.w3] [b.w1, b.w2, b.w3] bounded oddB
  have left := Int.mul_ediv_cancel_of_dvd divisible.1
  have right := Int.mul_ediv_cancel_of_dvd divisible.2
  change (2 : Int) ^ count * actual.1 = factors.f0 * (sourcePackedFourWords a : Int) + factors.g0 * (sourcePackedFourWords b : Int) at left
  change (2 : Int) ^ count * actual.2 = factors.f1 * (sourcePackedFourWords a : Int) + factors.g1 * (sourcePackedFourWords b : Int) at right
  exact ⟨an_exact_scaled_signed_row_derives_the_exact_sign_corrected_magnitude_row _ _ _ _ _ _ left,
    an_exact_scaled_signed_row_derives_the_exact_sign_corrected_magnitude_row _ _ _ _ _ _ right⟩

set_option pp.all true in
#check @sourceMagnitudeSign
#print axioms sourceMagnitudeSign
set_option pp.all true in
#check @source_magnitude_sign_times_its_value_is_the_exact_natural_magnitude
#print axioms source_magnitude_sign_times_its_value_is_the_exact_natural_magnitude
set_option pp.all true in
#check @an_exact_scaled_signed_row_derives_the_exact_sign_corrected_magnitude_row
#print axioms an_exact_scaled_signed_row_derives_the_exact_sign_corrected_magnitude_row
set_option pp.all true in
#check @original_full_input_prefixes_derive_both_exact_sign_corrected_magnitude_rows
#print axioms original_full_input_prefixes_derive_both_exact_sign_corrected_magnitude_rows
end ShielddSecurity.TransferBlstArmInverseMagnitudeRows01
