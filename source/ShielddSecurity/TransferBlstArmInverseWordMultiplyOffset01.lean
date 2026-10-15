import ShielddSecurity.TransferBlstArmInverseWordMultiplyValue01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordMultiplyOffset01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmCarryChains01 (sourceAddCarryChain)
open TransferBlstArmInverseWordMultiply01 (sourceMultiplyWordLow sourceMultiplyWordHigh)
attribute [local irreducible] sourceMultiplyWordLow sourceMultiplyWordHigh sourceAddCarryChain

/-! Parameterized top-word offset in the original partialsEquation-product carry
chain. The offset is an explicit source operand; its derivation from the
factor sign and native NEG instruction is a separate obligation. -/

def sourceOffsetWordMultiply (words : List UInt64) (multiplier topOffset : UInt64) : List UInt64 × Bool :=
  TransferBlstArmInverseShiftedWordAdd01.sourceShiftedProductCarry
    (words.map (fun word => sourceMultiplyWordLow word multiplier))
    (words.map (fun word => sourceMultiplyWordHigh word multiplier)) topOffset

theorem original_top_offset_product_retains_exactly_one_extra_word
    (words : List UInt64) (multiplier topOffset : UInt64) :
    (sourceOffsetWordMultiply words multiplier topOffset).1.length = words.length + 1 := by
  have generic := TransferBlstArmInverseShiftedWordAdd01.equal_length_shifted_partial_lists_derive_the_extra_output_word_count
    (words.map (fun word => sourceMultiplyWordLow word multiplier))
    (words.map (fun word => sourceMultiplyWordHigh word multiplier)) topOffset (by simp only [List.length_map])
  simpa only [List.length_map] using generic

theorem original_top_offset_product_conserves_the_entire_value_and_arithmetic_carry
    (words : List UInt64) (multiplier topOffset : UInt64) :
    packWords (sourceOffsetWordMultiply words multiplier topOffset).1 +
      radix64 ^ (words.length + 1) * (sourceOffsetWordMultiply words multiplier topOffset).2.toNat =
        packWords words * multiplier.toNat + radix64 ^ words.length * topOffset.toNat := by
  let lows := words.map (fun word => sourceMultiplyWordLow word multiplier)
  let highs := words.map (fun word => sourceMultiplyWordHigh word multiplier)
  have generic := TransferBlstArmInverseShiftedWordAdd01.equal_length_shifted_partial_lists_derive_the_entire_value_and_final_arithmetic_carry
    lows highs topOffset (by simp only [lows, highs, List.length_map])
  have lowLength : lows.length = words.length := by simp only [lows, List.length_map]
  rw [lowLength] at generic
  have partialsEquation := TransferBlstArmInverseWordMultiply01.symbolic_low_and_high_partial_product_lists_conserve_the_entire_packed_product words multiplier
  change packWords lows + radix64 * packWords highs = packWords words * multiplier.toNat at partialsEquation
  calc
    _ = packWords lows + radix64 ^ words.length * topOffset.toNat + radix64 * packWords highs := generic
    _ = (packWords lows + radix64 * packWords highs) + radix64 ^ words.length * topOffset.toNat := by ring1
    _ = _ := by rw [partialsEquation]

attribute [local irreducible] sourceOffsetWordMultiply

theorem original_top_offset_product_retains_the_entire_integer_residue_at_its_output_width
    (words : List UInt64) (multiplier topOffset : UInt64) :
    (packWords (sourceOffsetWordMultiply words multiplier topOffset).1 : Int) % ((radix64 ^ (words.length + 1) : Nat) : Int) =
      ((packWords words : Int) * (multiplier.toNat : Int) + ((radix64 ^ words.length : Nat) : Int) * (topOffset.toNat : Int)) %
        ((radix64 ^ (words.length + 1) : Nat) : Int) := by
  have conserved := original_top_offset_product_conserves_the_entire_value_and_arithmetic_carry words multiplier topOffset
  have cast := congrArg (fun value : Nat => (value : Int)) conserved
  simp only [Nat.cast_add, Nat.cast_mul] at cast
  have reduced := congrArg (fun value : Int => value % ((radix64 ^ (words.length + 1) : Nat) : Int)) cast
  dsimp only at reduced
  rw [Int.add_mul_emod_self_left] at reduced
  exact reduced

set_option pp.all true in
#check @sourceOffsetWordMultiply
#print axioms sourceOffsetWordMultiply
set_option pp.all true in
#check @original_top_offset_product_retains_exactly_one_extra_word
#print axioms original_top_offset_product_retains_exactly_one_extra_word
set_option pp.all true in
#check @original_top_offset_product_conserves_the_entire_value_and_arithmetic_carry
#print axioms original_top_offset_product_conserves_the_entire_value_and_arithmetic_carry
set_option pp.all true in
#check @original_top_offset_product_retains_the_entire_integer_residue_at_its_output_width
#print axioms original_top_offset_product_retains_the_entire_integer_residue_at_its_output_width
end ShielddSecurity.TransferBlstArmInverseWordMultiplyOffset01
