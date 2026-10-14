import ShielddSecurity.TransferBlstArmInverseAbsOdd01
import ShielddSecurity.TransferBlstArmInverseProgress01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseBatchOdd01
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (SourceFactors Tracks sourceFactorInitial sourceFactorWalk)
attribute [local irreducible] sourceFactorWalk packWords

/-! Arithmetic odd-second-input invariant of an original initialized31 batch.
The factors, exact division and absolute value are derived, not supplied.
High-window selection/progress, actual signed multiplication/shift/negation
word operations, coefficient production and native execution remain separate. -/

def sourceBatchFactors (count : Nat) (highA lowA highB lowB : UInt64) : SourceFactors :=
  sourceFactorWalk count (sourceFactorInitial
    (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB))

def sourceBatchSecondMagnitude (count : Nat) (highA lowA highB lowB : UInt64) (restA restB : List UInt64) : Nat :=
  let factors := sourceBatchFactors count highA lowA highB lowB
  ((factors.f1*(packWords (lowA::restA):Int)+factors.g1*(packWords (lowB::restB):Int))/2147483648).natAbs

theorem symbolic_initialized_batch_derives_odd_entire_second_magnitude
    (count : Nat) (positive : 1≤count) (scale : (2:Int)^count=2147483648)
    (highA lowA highB lowB : UInt64) (restA restB : List UInt64) (oddB : lowB.toNat%2=1) :
    sourceBatchSecondMagnitude count highA lowA highB lowB restA restB%2=1 := by
  let approxA := sourceApproxLow31 highA lowA
  let approxB := sourceApproxLow31 highB lowB
  let factors := sourceBatchFactors count highA lowA highB lowB
  have approximateOdd : (sourceFactorInitial approxA approxB).b%2=1 :=
    TransferBlstArmInverseApproxBits01.original_low31_approximation_preserves_oddness_of_the_original_low_word highB lowB oddB
  have tracked := TransferBlstArmInverseFactors01.original_initialized_factor_walk_derives_exact_scaled_input_rows
    count approxA approxB approximateOdd
  rw [scale] at tracked
  change Tracks approxA approxB 2147483648 factors at tracked
  have retained := TransferBlstArmInverseProgress01.original_exact_factor_walk_retains_odd_second_input
    count (sourceFactorInitial approxA approxB) approximateOdd
  change factors.b%2=1 at retained
  have previous : count-1+1=count := by omega
  have even := TransferBlstArmInverseApproxParity01.every_positive_original_factor_walk_derives_even_second_row_coefficients
    (count-1) (sourceFactorInitial approxA approxB)
  rw [previous] at even
  change factors.f1%2=0 ∧ factors.g1%2=0 at even
  rcases TransferBlstArmInverseApproxInput01.original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference highA lowA restA with ⟨deltaA,inputA⟩
  rcases TransferBlstArmInverseApproxInput01.original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference highB lowB restB with ⟨deltaB,inputB⟩
  have quotientOdd := TransferBlstArmInverseApproxParity01.original_even_second_factor_row_and_odd_approximate_input_preserve_full_quotient_oddness
    approxA approxB (packWords (lowA::restA):Int) (packWords (lowB::restB):Int)
    deltaA deltaB factors tracked inputA inputB even retained
  change ((factors.f1*(packWords (lowA::restA):Int)+factors.g1*(packWords (lowB::restB):Int))/2147483648).natAbs%2=1
  exact TransferBlstArmInverseAbsOdd01.odd_signed_integer_absolute_value_retains_oddness _ quotientOdd

theorem original_initialized_31_batch_derives_odd_entire_second_magnitude
    (highA lowA highB lowB : UInt64) (restA restB : List UInt64) (oddB : lowB.toNat%2=1) :
    sourceBatchSecondMagnitude 31 highA lowA highB lowB restA restB%2=1 := by
  exact symbolic_initialized_batch_derives_odd_entire_second_magnitude
    31 (by decide) (by decide +kernel) highA lowA highB lowB restA restB oddB

set_option pp.all true in
#check @sourceBatchFactors
#print axioms sourceBatchFactors
set_option pp.all true in
#check @sourceBatchSecondMagnitude
#print axioms sourceBatchSecondMagnitude
set_option pp.all true in
#check @symbolic_initialized_batch_derives_odd_entire_second_magnitude
#print axioms symbolic_initialized_batch_derives_odd_entire_second_magnitude
set_option pp.all true in
#check @original_initialized_31_batch_derives_odd_entire_second_magnitude
#print axioms original_initialized_31_batch_derives_odd_entire_second_magnitude
end ShielddSecurity.TransferBlstArmInverseBatchOdd01
