import ShielddSecurity.TransferBlstArmInverseBatchOdd01
import ShielddSecurity.TransferBlstArmInverseNorm01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseBatchBounds01
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseBatchOdd01 (sourceBatchFactors sourceBatchSecondMagnitude)
attribute [local irreducible] sourceFactorWalk packWords

/-! Entire original batch input/output magnitude bounds from raw four-word
width, initialized row norms and exact full-input row division. No chosen
output magnitude or factor bounds are supplied. Actual word multiplication,
shift/absolute value, high-window progress and native execution remain open. -/

def sourceBatchFirstMagnitude (count : Nat) (highA lowA highB lowB : UInt64) (restA restB : List UInt64) : Nat :=
  let factors := sourceBatchFactors count highA lowA highB lowB
  ((factors.f0*(packWords (lowA::restA):Int)+factors.g0*(packWords (lowB::restB):Int))/2147483648).natAbs

theorem raw_four_word_input_derives_its_entire_signed_magnitude_bound
    (low : UInt64) (rest : List UInt64) (width : (low::rest).length=4) :
    (packWords (low::rest):Int).natAbs ≤ radix64^4-1 := by
  have bounded := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (low::rest)
  rw [width] at bounded
  simp only [Int.natAbs_natCast]
  omega

theorem bounded_inputs_and_factor_row_norm_bound_the_exact_divided_magnitude
    (inputA inputB f g : Int) (bound : Nat)
    (left : inputA.natAbs ≤ bound) (right : inputB.natAbs ≤ bound)
    (row : f.natAbs+g.natAbs ≤ 2147483648)
    (exactDivision : (2147483648:Int) ∣ f*inputA+g*inputB) :
    ((f*inputA+g*inputB)/2147483648).natAbs ≤ bound := by
  have bounded := TransferBlstArmInverseNorm01.bounded_signed_inputs_and_factor_row_derive_the_actual_linear_combination_bound
    inputA inputB f g bound 2147483648 left right row
  have whole : f*inputA+g*inputB=inputA*f+inputB*g := by ring
  rw [whole] at exactDivision ⊢
  rw [Int.natAbs_ediv_of_dvd exactDivision]
  change (inputA*f+inputB*g).natAbs/2147483648 ≤ bound
  calc
    _ ≤ (bound*2147483648)/2147483648 := Nat.div_le_div_right bounded
    _ = bound := Nat.mul_div_left bound (by decide)

theorem symbolic_initialized_batch_derives_both_complete_four_limb_output_ranges
    (count : Nat) (scale : (2:Nat)^count=2147483648)
    (highA lowA highB lowB : UInt64) (restA restB : List UInt64)
    (widthA : (lowA::restA).length=4) (widthB : (lowB::restB).length=4)
    (oddB : lowB.toNat%2=1) :
    sourceBatchFirstMagnitude count highA lowA highB lowB restA restB < radix64^4 ∧
    sourceBatchSecondMagnitude count highA lowA highB lowB restA restB < radix64^4 := by
  let factors := sourceBatchFactors count highA lowA highB lowB
  have rows := TransferBlstArmInverseNorm01.original_initialized_factor_walk_derives_row_sums_at_most_its_radix_power
    count (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB)
  rw [scale] at rows
  change TransferBlstArmInverseNorm01.RowBounds 2147483648 factors at rows
  have approximateOdd := TransferBlstArmInverseApproxBits01.original_low31_approximation_preserves_oddness_of_the_original_low_word highB lowB oddB
  have tracked := TransferBlstArmInverseFactors01.original_initialized_factor_walk_derives_exact_scaled_input_rows
    count (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB) approximateOdd
  have scaleInt : (2:Int)^count=2147483648 := by exact_mod_cast scale
  rw [scaleInt] at tracked
  change TransferBlstArmInverseFactors01.Tracks (sourceApproxLow31 highA lowA)
    (sourceApproxLow31 highB lowB) 2147483648 factors at tracked
  rcases TransferBlstArmInverseApproxInput01.original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference highA lowA restA with ⟨deltaA,inputA⟩
  rcases TransferBlstArmInverseApproxInput01.original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference highB lowB restB with ⟨deltaB,inputB⟩
  have divided := TransferBlstArmInverseApproxRows01.tracked_factor_rows_and_exact_input_lifts_derive_both_entire_divisible_rows
    (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB) 2147483648
    (packWords (lowA::restA):Int) (packWords (lowB::restB):Int) deltaA deltaB factors tracked inputA inputB
  rcases divided with ⟨⟨first,firstDivision⟩,⟨second,secondDivision⟩⟩
  have left := raw_four_word_input_derives_its_entire_signed_magnitude_bound lowA restA widthA
  have right := raw_four_word_input_derives_its_entire_signed_magnitude_bound lowB restB widthB
  have firstBound := bounded_inputs_and_factor_row_norm_bound_the_exact_divided_magnitude
    (packWords (lowA::restA):Int) (packWords (lowB::restB):Int) factors.f0 factors.g0
    (radix64^4-1) left right rows.1 ⟨first,firstDivision⟩
  have secondBound := bounded_inputs_and_factor_row_norm_bound_the_exact_divided_magnitude
    (packWords (lowA::restA):Int) (packWords (lowB::restB):Int) factors.f1 factors.g1
    (radix64^4-1) left right rows.2 ⟨second,secondDivision⟩
  have positive : 0<radix64^4 := by decide +kernel
  change ((factors.f0*(packWords (lowA::restA):Int)+factors.g0*(packWords (lowB::restB):Int))/2147483648).natAbs < radix64^4 ∧
    ((factors.f1*(packWords (lowA::restA):Int)+factors.g1*(packWords (lowB::restB):Int))/2147483648).natAbs < radix64^4
  constructor <;> omega

theorem original_initialized_31_batch_derives_both_complete_four_limb_output_ranges
    (highA lowA highB lowB : UInt64) (restA restB : List UInt64)
    (widthA : (lowA::restA).length=4) (widthB : (lowB::restB).length=4)
    (oddB : lowB.toNat%2=1) :
    sourceBatchFirstMagnitude 31 highA lowA highB lowB restA restB < radix64^4 ∧
    sourceBatchSecondMagnitude 31 highA lowA highB lowB restA restB < radix64^4 := by
  exact symbolic_initialized_batch_derives_both_complete_four_limb_output_ranges
    31 (by decide +kernel) highA lowA highB lowB restA restB widthA widthB oddB

set_option pp.all true in
#check @sourceBatchFirstMagnitude
#print axioms sourceBatchFirstMagnitude
set_option pp.all true in
#check @raw_four_word_input_derives_its_entire_signed_magnitude_bound
#print axioms raw_four_word_input_derives_its_entire_signed_magnitude_bound
set_option pp.all true in
#check @bounded_inputs_and_factor_row_norm_bound_the_exact_divided_magnitude
#print axioms bounded_inputs_and_factor_row_norm_bound_the_exact_divided_magnitude
set_option pp.all true in
#check @symbolic_initialized_batch_derives_both_complete_four_limb_output_ranges
#print axioms symbolic_initialized_batch_derives_both_complete_four_limb_output_ranges
set_option pp.all true in
#check @original_initialized_31_batch_derives_both_complete_four_limb_output_ranges
#print axioms original_initialized_31_batch_derives_both_complete_four_limb_output_ranges
end ShielddSecurity.TransferBlstArmInverseBatchBounds01
