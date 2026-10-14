import ShielddSecurity.TransferBlstArmInverseApproxRows01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePrefixDiv01
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
attribute [local irreducible] sourceFactorWalk packWords

/-! Every prefix of the original initialized31 factor walk divides both
entire input rows exactly. Low31 lifts and original parity-controlled row
tracking derive divisibility; no chosen coefficient or quotient is supplied.
High-window correspondence, approximate progress and native execution remain
separate. This supports later error propagation at the first divergent step. -/

theorem original_low31_radix_is_an_exact_multiple_of_each_prefix_radix
    (count : Nat) (bounded : count <= 31) :
    (2147483648:Int)=((2:Int)^count)*((2:Int)^(31-count)) := by
  have sum : count+(31-count)=31 := by omega
  calc
    _ = (2:Int)^31 := by decide +kernel
    _ = (2:Int)^(count+(31-count)) := by rw [sum]
    _ = _ := by rw [Int.pow_add]

theorem original_full_low31_input_lift_derives_an_exact_lift_for_every_prefix
    (count approx : Nat) (input delta : Int) (bounded : count <= 31)
    (lifted : input=(approx:Int)+2147483648*delta) :
    ∃ prefixDelta : Int, input=(approx:Int)+((2:Int)^count)*prefixDelta := by
  refine ⟨((2:Int)^(31-count))*delta,?_⟩
  rw [lifted,original_low31_radix_is_an_exact_multiple_of_each_prefix_radix count bounded]
  rw [Int.mul_assoc]

theorem original_initialized_factor_prefixes_divide_both_entire_input_rows
    (count : Nat) (highA lowA highB lowB : UInt64) (restA restB : List UInt64)
    (bounded : count <= 31) (oddB : lowB.toNat%2=1) :
    let factors := sourceFactorWalk count (sourceFactorInitial
      (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB));
    (((2:Int)^count) ∣ factors.f0*(packWords (lowA::restA):Int)+
      factors.g0*(packWords (lowB::restB):Int)) /\
    (((2:Int)^count) ∣ factors.f1*(packWords (lowA::restA):Int)+
      factors.g1*(packWords (lowB::restB):Int)) := by
  dsimp only
  rcases TransferBlstArmInverseApproxInput01.original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference highA lowA restA with ⟨deltaA,left⟩
  rcases TransferBlstArmInverseApproxInput01.original_full_input_and_low31_approximation_have_an_exact_signed_radix_difference highB lowB restB with ⟨deltaB,right⟩
  rcases original_full_low31_input_lift_derives_an_exact_lift_for_every_prefix count
    (sourceApproxLow31 highA lowA) (packWords (lowA::restA):Int) deltaA bounded left with ⟨prefixA,inputA⟩
  rcases original_full_low31_input_lift_derives_an_exact_lift_for_every_prefix count
    (sourceApproxLow31 highB lowB) (packWords (lowB::restB):Int) deltaB bounded right with ⟨prefixB,inputB⟩
  have tracked := TransferBlstArmInverseFactors01.original_initialized_factor_walk_derives_exact_scaled_input_rows count
    (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB)
    (TransferBlstArmInverseApproxBits01.original_low31_approximation_preserves_oddness_of_the_original_low_word highB lowB oddB)
  exact TransferBlstArmInverseApproxRows01.tracked_factor_rows_and_exact_input_lifts_derive_both_entire_divisible_rows
    (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB) ((2:Int)^count)
    (packWords (lowA::restA):Int) (packWords (lowB::restB):Int) prefixA prefixB
    (sourceFactorWalk count (sourceFactorInitial (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB)))
    tracked inputA inputB

set_option pp.all true in
#check @original_low31_radix_is_an_exact_multiple_of_each_prefix_radix
#print axioms original_low31_radix_is_an_exact_multiple_of_each_prefix_radix
set_option pp.all true in
#check @original_full_low31_input_lift_derives_an_exact_lift_for_every_prefix
#print axioms original_full_low31_input_lift_derives_an_exact_lift_for_every_prefix
set_option pp.all true in
#check @original_initialized_factor_prefixes_divide_both_entire_input_rows
#print axioms original_initialized_factor_prefixes_divide_both_entire_input_rows
end ShielddSecurity.TransferBlstArmInversePrefixDiv01
