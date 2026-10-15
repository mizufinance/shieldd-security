import ShielddSecurity.TransferBlstArmInverseWordMultiply01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordMultiplyCarry01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmCarryChains01 (sourceAddCarryChain)
open TransferBlstArmInverseWordMultiply01 (sourceMultiplyWordLow sourceMultiplyWordHigh symbolic_low_and_high_partial_product_lists_conserve_the_entire_packed_product)
attribute [local irreducible] sourceMultiplyWordLow sourceMultiplyWordHigh sourceAddCarryChain

/-! Original shifted partial-product carry chain, using separately qualified
low/high product arithmetic. Actual native flags/ISA remain separate. -/

def sourceUnsignedWordMultiply (words : List UInt64) (multiplier : UInt64) : List UInt64 × Bool :=
  sourceAddCarryChain false
    (((words.map (fun word => sourceMultiplyWordLow word multiplier)) ++ [0]).zip
      (0 :: words.map (fun word => sourceMultiplyWordHigh word multiplier)))

theorem original_unsigned_word_product_retains_one_extra_output_word
    (words : List UInt64) (multiplier : UInt64) :
    (sourceUnsignedWordMultiply words multiplier).1.length = words.length + 1 := by
  simp only [sourceUnsignedWordMultiply, TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
    List.length_zip, List.length_append, List.length_map, List.length_cons, List.length_nil, Nat.min_self]

set_option pp.all true in
#check @sourceUnsignedWordMultiply
#print axioms sourceUnsignedWordMultiply
set_option pp.all true in
#check @original_unsigned_word_product_retains_one_extra_output_word
#print axioms original_unsigned_word_product_retains_one_extra_output_word
end ShielddSecurity.TransferBlstArmInverseWordMultiplyCarry01
