import ShielddSecurity.TransferBlstArmInverseWordMultiplyCarry01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseShiftedWordAdd01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmCarryChains01 (sourceAddCarryChain)
attribute [local irreducible] sourceAddCarryChain

/-! Generic shifted-list carry equation. The low/high lists remain arbitrary,
so proof rewriting cannot unfold a concrete word-product producer. Native
instruction execution and source-list origins remain separate. -/

def sourceShiftedProductCarry (lows highs : List UInt64) (topOffset : UInt64) : List UInt64 × Bool :=
  sourceAddCarryChain false ((lows ++ [topOffset]).zip (0 :: highs))

theorem equal_length_shifted_partial_lists_derive_the_extra_output_word_count
    (lows highs : List UInt64) (topOffset : UInt64) (same : lows.length = highs.length) :
    (sourceShiftedProductCarry lows highs topOffset).1.length = lows.length + 1 := by
  simp only [sourceShiftedProductCarry, TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
    List.length_zip, List.length_append, List.length_cons, List.length_nil, same, Nat.min_self]

theorem equal_length_shifted_partial_lists_derive_the_entire_value_and_final_arithmetic_carry
    (lows highs : List UInt64) (topOffset : UInt64) (same : lows.length = highs.length) :
    packWords (sourceShiftedProductCarry lows highs topOffset).1 +
      radix64 ^ (lows.length + 1) * (sourceShiftedProductCarry lows highs topOffset).2.toNat =
        packWords lows + radix64 ^ lows.length * topOffset.toNat + radix64 * packWords highs := by
  have lowLength : (lows ++ [topOffset]).length = lows.length + 1 := by
    simp only [List.length_append, List.length_singleton]
  have highLength : (0 :: highs).length = highs.length + 1 := by
    simp only [List.length_cons]
  have leftProjection : (lows ++ [topOffset]).length ≤ (0 :: highs).length := by
    rw [lowLength, highLength, same]
  have rightProjection : (0 :: highs).length ≤ (lows ++ [topOffset]).length := by
    rw [lowLength, highLength, same]
  have conserved := TransferBlstArmCarryChains01.symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    false ((lows ++ [topOffset]).zip (0 :: highs))
  rw [List.map_fst_zip leftProjection, List.map_snd_zip rightProjection,
    List.length_zip, lowLength, highLength, same, Nat.min_self,
    TransferBlstArmInverseFirst01.symbolic_word_append_has_the_entire_radix_weighted_value] at conserved
  have oneWord : packWords [topOffset] = topOffset.toNat := by
    simp only [packWords, Nat.mul_zero, Nat.add_zero]
  have shifted : packWords (0 :: highs) = radix64 * packWords highs := by
    simp only [packWords, UInt64.toNat_zero, Nat.zero_add]
  rw [oneWord, shifted] at conserved
  change packWords (sourceShiftedProductCarry lows highs topOffset).1 +
    radix64 ^ (highs.length + 1) * (sourceShiftedProductCarry lows highs topOffset).2.toNat =
      packWords lows + radix64 ^ lows.length * topOffset.toNat + radix64 * packWords highs + 0 at conserved
  rw [←same, Nat.add_zero] at conserved
  exact conserved

set_option pp.all true in
#check @sourceShiftedProductCarry
#print axioms sourceShiftedProductCarry
set_option pp.all true in
#check @equal_length_shifted_partial_lists_derive_the_extra_output_word_count
#print axioms equal_length_shifted_partial_lists_derive_the_extra_output_word_count
set_option pp.all true in
#check @equal_length_shifted_partial_lists_derive_the_entire_value_and_final_arithmetic_carry
#print axioms equal_length_shifted_partial_lists_derive_the_entire_value_and_final_arithmetic_carry
end ShielddSecurity.TransferBlstArmInverseShiftedWordAdd01
