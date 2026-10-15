import ShielddSecurity.TransferBlstArmCarryChains01
import ShielddSecurity.TransferBlstArmInverseSignedWordPrepare01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseCarrySplit01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmCarryChains01 (sourceAddCarry sourceAddCarryChain)
open TransferBlstArmInverseSignedWordPrepare01 (sourceMaskPreparedWords)
attribute [local irreducible] sourceAddCarry

/-! Source carry chains may pause at any symbolic word boundary and resume
with the actual captured arithmetic flag. This is the arithmetic basis for
the split coefficient-product routines; their operand layouts and compiled
execution are separate obligations. -/

theorem every_symbolic_source_carry_chain_can_pause_and_resume_with_its_actual_flag
    (low high : List (UInt64 × UInt64)) (carry : Bool) :
    sourceAddCarryChain carry (low ++ high) =
      let first := sourceAddCarryChain carry low
      let last := sourceAddCarryChain first.2 high
      (first.1 ++ last.1, last.2) := by
  induction low generalizing carry with
  | nil => simp only [List.nil_append, sourceAddCarryChain]
  | cons pair rest ih =>
    simp only [List.cons_append, sourceAddCarryChain, ih]

attribute [local irreducible] sourceAddCarryChain

theorem every_symbolic_word_split_conserves_both_entire_packed_values
    (low high : List UInt64) :
    packWords (low ++ high) = packWords low + radix64 ^ low.length * packWords high := by
  induction low with
  | nil => simp only [List.nil_append, packWords, List.length_nil, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | cons word rest ih =>
    change word.toNat + radix64 * packWords (rest ++ high) =
      word.toNat + radix64 * packWords rest + radix64 ^ (rest.length + 1) * packWords high
    rw [ih, Nat.pow_succ]
    ring1

theorem the_entire_low_word_block_is_the_exact_full_value_residue_at_its_boundary
    (low high : List UInt64) :
    packWords (low ++ high) % radix64 ^ low.length = packWords low := by
  have bounded := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power low
  rw [every_symbolic_word_split_conserves_both_entire_packed_values,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bounded]

theorem the_entire_high_word_block_is_the_exact_full_value_quotient_at_its_boundary
    (low high : List UInt64) :
    packWords (low ++ high) / radix64 ^ low.length = packWords high := by
  have bounded := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power low
  have positive : 0 < radix64 ^ low.length := Nat.pow_pos (by decide)
  rw [every_symbolic_word_split_conserves_both_entire_packed_values, Nat.add_mul_div_left _ _ positive]
  rw [Nat.div_eq_of_lt bounded, Nat.zero_add]

theorem every_source_captured_low_block_and_resumed_high_block_retain_the_complete_original_word_count
    (low high : List (UInt64 × UInt64)) (carry : Bool) :
    ((sourceAddCarryChain carry low).1 ++
      (sourceAddCarryChain (sourceAddCarryChain carry low).2 high).1).length = low.length + high.length := by
  rw [List.length_append,
    TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
    TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count]

def sourceMaskOperandPairs (words : List UInt64) (mask : UInt64) : List (UInt64 × UInt64) :=
  words.map (fun word => (word ^^^ mask, 0))

theorem the_original_masked_zero_operand_list_is_exactly_the_symbolic_pair_map
    (words : List UInt64) (mask : UInt64) :
    sourceMaskOperandPairs words mask =
      (words.map (fun word => word ^^^ mask)).zip (List.replicate words.length (0 : UInt64)) := by
  unfold sourceMaskOperandPairs
  induction words with
  | nil => rfl
  | cons word rest ih =>
    simp only [List.map_cons, List.length_cons, List.replicate_succ, List.zip_cons_cons, ih]

theorem every_original_mask_preparation_can_pause_and_resume_with_its_actual_captured_carry
    (low high : List UInt64) (mask : UInt64) :
    sourceMaskPreparedWords (low ++ high) mask =
      let first := sourceMaskPreparedWords low mask
      let last := sourceAddCarryChain first.2 (sourceMaskOperandPairs high mask)
      (first.1 ++ last.1, last.2) := by
  unfold sourceMaskPreparedWords
  simp only [← the_original_masked_zero_operand_list_is_exactly_the_symbolic_pair_map]
  have append : sourceMaskOperandPairs (low ++ high) mask =
      sourceMaskOperandPairs low mask ++ sourceMaskOperandPairs high mask := List.map_append
  rw [append]
  exact every_symbolic_source_carry_chain_can_pause_and_resume_with_its_actual_flag _ _ _

set_option pp.all true in
#check @every_symbolic_source_carry_chain_can_pause_and_resume_with_its_actual_flag
#print axioms every_symbolic_source_carry_chain_can_pause_and_resume_with_its_actual_flag
set_option pp.all true in
#check @every_symbolic_word_split_conserves_both_entire_packed_values
#print axioms every_symbolic_word_split_conserves_both_entire_packed_values
set_option pp.all true in
#check @the_entire_low_word_block_is_the_exact_full_value_residue_at_its_boundary
#print axioms the_entire_low_word_block_is_the_exact_full_value_residue_at_its_boundary
set_option pp.all true in
#check @the_entire_high_word_block_is_the_exact_full_value_quotient_at_its_boundary
#print axioms the_entire_high_word_block_is_the_exact_full_value_quotient_at_its_boundary
set_option pp.all true in
#check @every_source_captured_low_block_and_resumed_high_block_retain_the_complete_original_word_count
#print axioms every_source_captured_low_block_and_resumed_high_block_retain_the_complete_original_word_count
set_option pp.all true in
#check @sourceMaskOperandPairs
#print axioms sourceMaskOperandPairs
set_option pp.all true in
#check @the_original_masked_zero_operand_list_is_exactly_the_symbolic_pair_map
#print axioms the_original_masked_zero_operand_list_is_exactly_the_symbolic_pair_map
set_option pp.all true in
#check @every_original_mask_preparation_can_pause_and_resume_with_its_actual_captured_carry
#print axioms every_original_mask_preparation_can_pause_and_resume_with_its_actual_captured_carry
end ShielddSecurity.TransferBlstArmInverseCarrySplit01
