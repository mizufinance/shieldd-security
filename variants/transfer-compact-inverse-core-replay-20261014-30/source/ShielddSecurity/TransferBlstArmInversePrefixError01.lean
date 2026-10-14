import ShielddSecurity.TransferBlstArmInverseApproxError01
import ShielddSecurity.TransferBlstArmInverseErrorRows01
import ShielddSecurity.TransferBlstArmInversePrefixDiv01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePrefixError01
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
attribute [local irreducible] sourceFactorWalk packWords sourceActualFactorQuotients

/-! Full original limb-input approximation error at every initialized prefix.
Exact row divisibility is derived from original low31 lifts, not assumed.
The sole window correspondence premises are explicit whole-input high-word
quotients; actual CLZ/window selection and first-divergence progress still
require separate proofs. Compiled execution/native certification stay open. -/

theorem original_entire_input_factor_prefixes_preserve_both_initial_window_error_bounds
    (count shift : Nat) (highA lowA highB lowB : UInt64) (restA restB : List UInt64)
    (bounded : count <= 31) (oddB : lowB.toNat%2=1)
    (highWindowA : highA.toNat=packWords (lowA::restA)/2^shift)
    (highWindowB : highB.toNat=packWords (lowB::restB)/2^shift) :
    let factors := sourceFactorWalk count (sourceFactorInitial
      (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB));
    let actual := sourceActualFactorQuotients count
      (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB)
      (packWords (lowA::restA):Int) (packWords (lowB::restB):Int);
    (actual.1-((2^shift:Nat):Int)*(factors.a:Int)).natAbs <= 2^shift*2147483648 /\
    (actual.2-((2^shift:Nat):Int)*(factors.b:Int)).natAbs <= 2^shift*2147483648 := by
  dsimp only
  have divisible := TransferBlstArmInversePrefixDiv01.original_initialized_factor_prefixes_divide_both_entire_input_rows
    count highA lowA highB lowB restA restB bounded oddB
  have first := TransferBlstArmInverseApproxError01.original_low31_replacement_has_strict_initial_scaled_integer_error
    (packWords (lowA::restA)) shift highA lowA highWindowA
  have second := TransferBlstArmInverseApproxError01.original_low31_replacement_has_strict_initial_scaled_integer_error
    (packWords (lowB::restB)) shift highB lowB highWindowB
  have leftError : ((packWords (lowA::restA):Int)-((2^shift:Nat):Int)*(sourceApproxLow31 highA lowA:Int)).natAbs <= 2^shift*2147483648 := by
    simpa only [Int.natCast_mul] using (Nat.le_of_lt first)
  have rightError : ((packWords (lowB::restB):Int)-((2^shift:Nat):Int)*(sourceApproxLow31 highB lowB:Int)).natAbs <= 2^shift*2147483648 := by
    simpa only [Int.natCast_mul] using (Nat.le_of_lt second)
  exact TransferBlstArmInverseErrorRows01.original_initialized_factor_quotients_preserve_both_full_input_error_bounds
    count (sourceApproxLow31 highA lowA) (sourceApproxLow31 highB lowB) (2^shift*2147483648)
    (packWords (lowA::restA):Int) (packWords (lowB::restB):Int) ((2^shift:Nat):Int)
    (TransferBlstArmInverseApproxBits01.original_low31_approximation_preserves_oddness_of_the_original_low_word highB lowB oddB)
    leftError rightError divisible.1 divisible.2

set_option pp.all true in
#check @original_entire_input_factor_prefixes_preserve_both_initial_window_error_bounds
#print axioms original_entire_input_factor_prefixes_preserve_both_initial_window_error_bounds
end ShielddSecurity.TransferBlstArmInversePrefixError01
