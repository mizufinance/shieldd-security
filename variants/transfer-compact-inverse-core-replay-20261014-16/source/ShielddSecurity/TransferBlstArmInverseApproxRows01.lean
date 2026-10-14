import ShielddSecurity.TransferBlstArmInverseApproxInput01
import ShielddSecurity.TransferBlstArmInverseFactors01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseApproxRows01
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseApproxBits01
  (sourceApproxLow31 original_low31_approximation_preserves_oddness_of_the_original_low_word)
open TransferBlstArmInverseApproxInput01
  (original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference)
open TransferBlstArmInverseFactors01
  (SourceFactors Tracks sourceFactorInitial sourceFactorWalk
   original_initialized_factor_walk_derives_exact_scaled_input_rows)
attribute [local irreducible] sourceFactorWalk packWords

/-! Both complete original input rows are divisible by the original 31-step
shift radix. The factor rows are derived from original initialized updates,
not chosen. Full limb input lifts derive from the actual low31 replacement.
High-window construction/error/progress, exact native multiply/shift and
coefficient production/native execution remain separate. -/

theorem tracked_factor_rows_and_exact_input_lifts_derive_both_entire_divisible_rows
    (approxA approxB : Nat) (scale inputA inputB deltaA deltaB : Int) (s : SourceFactors)
    (tracked : Tracks approxA approxB scale s)
    (left : inputA=(approxA:Int)+scale*deltaA)
    (right : inputB=(approxB:Int)+scale*deltaB) :
    (∃ quotient : Int, s.f0*inputA+s.g0*inputB=scale*quotient) ∧
    (∃ quotient : Int, s.f1*inputA+s.g1*inputB=scale*quotient) := by
  constructor
  · refine ⟨(s.a:Int)+s.f0*deltaA+s.g0*deltaB,?_⟩
    rw [left,right]
    calc
      _ = (s.f0*(approxA:Int)+s.g0*(approxB:Int))+scale*(s.f0*deltaA+s.g0*deltaB) := by
        simp only [Int.mul_add, Int.mul_left_comm, Int.add_assoc, Int.add_left_comm, Int.add_comm]
      _ = _ := by rw [← tracked.1]; simp only [Int.mul_add, Int.add_assoc]
  · refine ⟨(s.b:Int)+s.f1*deltaA+s.g1*deltaB,?_⟩
    rw [left,right]
    calc
      _ = (s.f1*(approxA:Int)+s.g1*(approxB:Int))+scale*(s.f1*deltaA+s.g1*deltaB) := by
        simp only [Int.mul_add, Int.mul_left_comm, Int.add_assoc, Int.add_left_comm, Int.add_comm]
      _ = _ := by rw [← tracked.2]; simp only [Int.mul_add, Int.add_assoc]

theorem original_31_factor_rows_divide_both_entire_inputs_without_losing_low_bits
    (highA lowA highB lowB : UInt64) (restA restB : List UInt64) (oddB : lowB.toNat%2=1) :
    let factors := sourceFactorWalk 31 (sourceFactorInitial
      (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB));
    (∃ quotient : Int, factors.f0*(packWords (lowA::restA):Int)+
      factors.g0*(packWords (lowB::restB):Int)=2147483648*quotient) ∧
    (∃ quotient : Int, factors.f1*(packWords (lowA::restA):Int)+
      factors.g1*(packWords (lowB::restB):Int)=2147483648*quotient) := by
  dsimp only
  rcases original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference highA lowA restA with ⟨deltaA,inputA⟩
  rcases original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference highB lowB restB with ⟨deltaB,inputB⟩
  have tracked := original_initialized_factor_walk_derives_exact_scaled_input_rows 31
    (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB)
    (original_low31_approximation_preserves_oddness_of_the_original_low_word highB lowB oddB)
  have scale : (2:Int)^31=2147483648 := by decide +kernel
  rw [scale] at tracked
  exact tracked_factor_rows_and_exact_input_lifts_derive_both_entire_divisible_rows
    (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB) 2147483648
    (packWords (lowA::restA):Int) (packWords (lowB::restB):Int) deltaA deltaB
    (sourceFactorWalk 31 (sourceFactorInitial (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB)))
    tracked inputA inputB

set_option pp.all true in
#check @tracked_factor_rows_and_exact_input_lifts_derive_both_entire_divisible_rows
#print axioms tracked_factor_rows_and_exact_input_lifts_derive_both_entire_divisible_rows
set_option pp.all true in
#check @original_31_factor_rows_divide_both_entire_inputs_without_losing_low_bits
#print axioms original_31_factor_rows_divide_both_entire_inputs_without_losing_low_bits
end ShielddSecurity.TransferBlstArmInverseApproxRows01
