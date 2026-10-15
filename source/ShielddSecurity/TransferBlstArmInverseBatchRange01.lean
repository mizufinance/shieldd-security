import ShielddSecurity.TransferBlstArmInverseWordRepack01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseBatchRange01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)

/-! Original signed source batch outputs fit the original four-word capacity.
The maximum never grows, including mismatches. This justifies exact source
repacking between batches; native multiply/carry/shift and stores stay open. -/

theorem original_four_word_packing_is_strictly_below_two256
    (input : SourceFourWords) : sourcePackedFourWords input < 2 ^ 256 := by
  have bound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power [input.w0, input.w1, input.w2, input.w3]
  have power : TransferScalarSerializationRange01.radix64 ^ 4 = (2 : Nat) ^ 256 := by
    simp only [TransferScalarSerializationRange01.radix64, ←Nat.pow_mul]
  change sourcePackedFourWords input < TransferScalarSerializationRange01.radix64 ^ 4 at bound
  rw [power] at bound
  exact bound

theorem initialized_zero_prefix_full_quotients_are_the_original_inputs
    (approxA approxB : Nat) (inputA inputB : Int) :
    sourceActualFactorQuotients 0 approxA approxB inputA inputB = (inputA, inputB) := by
  change ((1 * inputA + 0 * inputB) / 1, (0 * inputA + 1 * inputB) / 1) = (inputA, inputB)
  simp only [Int.one_mul, Int.zero_mul, Int.add_zero, Int.zero_add, Int.ediv_one]

theorem every_original31_step_full_output_maximum_is_at_most_the_initial_maximum
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    let final := sourceActualFactorQuotients 31
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    max final.1.natAbs final.2.natAbs ≤ max (sourcePackedFourWords a) (sourcePackedFourWords b) := by
  dsimp only
  have monotone := TransferBlstArmInverseSharpLasting01.original_signed_quotient_maximum_never_increases_from_any_earlier_prefix_through31
    0 31 a b (by decide) oddB
  dsimp only at monotone
  rw [initialized_zero_prefix_full_quotients_are_the_original_inputs] at monotone
  exact monotone

theorem every_original31_step_full_output_magnitude_fits_four_words
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    let final := sourceActualFactorQuotients 31
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    final.1.natAbs < 2 ^ 256 ∧ final.2.natAbs < 2 ^ 256 := by
  dsimp only
  have monotone := every_original31_step_full_output_maximum_is_at_most_the_initial_maximum a b oddB
  dsimp only at monotone
  have bound : max (sourcePackedFourWords a) (sourcePackedFourWords b) < 2 ^ 256 :=
    Nat.max_lt.mpr ⟨original_four_word_packing_is_strictly_below_two256 a, original_four_word_packing_is_strictly_below_two256 b⟩
  have both := Nat.lt_of_le_of_lt monotone bound
  exact ⟨Nat.lt_of_le_of_lt (Nat.le_max_left _ _) both, Nat.lt_of_le_of_lt (Nat.le_max_right _ _) both⟩

set_option pp.all true in
#check @original_four_word_packing_is_strictly_below_two256
#print axioms original_four_word_packing_is_strictly_below_two256
set_option pp.all true in
#check @initialized_zero_prefix_full_quotients_are_the_original_inputs
#print axioms initialized_zero_prefix_full_quotients_are_the_original_inputs
set_option pp.all true in
#check @every_original31_step_full_output_maximum_is_at_most_the_initial_maximum
#print axioms every_original31_step_full_output_maximum_is_at_most_the_initial_maximum
set_option pp.all true in
#check @every_original31_step_full_output_magnitude_fits_four_words
#print axioms every_original31_step_full_output_magnitude_fits_four_words
end ShielddSecurity.TransferBlstArmInverseBatchRange01
