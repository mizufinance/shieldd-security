import ShielddSecurity.TransferBlstArmInverseShiftedWordAdd01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordMultiplyValue01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmCarryChains01 (sourceAddCarryChain)
open TransferBlstArmInverseWordMultiply01 (sourceMultiplyWordLow sourceMultiplyWordHigh symbolic_low_and_high_partial_product_lists_conserve_the_entire_packed_product)
open TransferBlstArmInverseWordMultiplyCarry01 (sourceUnsignedWordMultiply)
attribute [local irreducible] sourceMultiplyWordLow sourceMultiplyWordHigh sourceAddCarryChain

/-! Complete unsigned product conservation from the original source carry
model; recursive implementations stay opaque outside explicit rewrites. -/

theorem original_shifted_partial_product_carry_chain_conserves_the_entire_unsigned_product
    (words : List UInt64) (multiplier : UInt64) :
    packWords (sourceUnsignedWordMultiply words multiplier).1 +
      radix64 ^ (words.length + 1) * (sourceUnsignedWordMultiply words multiplier).2.toNat = packWords words * multiplier.toNat := by
  let lows := words.map (fun word => sourceMultiplyWordLow word multiplier)
  let highs := words.map (fun word => sourceMultiplyWordHigh word multiplier)
  have same : lows.length = highs.length := by simp only [lows, highs, List.length_map]
  have generic := TransferBlstArmInverseShiftedWordAdd01.equal_length_shifted_partial_lists_derive_the_entire_value_and_final_arithmetic_carry
    lows highs 0 same
  have lowLength : lows.length = words.length := by simp only [lows, List.length_map]
  rw [lowLength, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at generic
  exact generic.trans (symbolic_low_and_high_partial_product_lists_conserve_the_entire_packed_product words multiplier)

set_option pp.all true in
#check @original_shifted_partial_product_carry_chain_conserves_the_entire_unsigned_product
#print axioms original_shifted_partial_product_carry_chain_conserves_the_entire_unsigned_product
end ShielddSecurity.TransferBlstArmInverseWordMultiplyValue01
