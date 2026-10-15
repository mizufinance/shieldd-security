import ShielddSecurity.TransferBlstArmInverseWordMultiplyOffset01
import ShielddSecurity.TransferBlstArmInverseWordMultiplyOverflow01
import ShielddSecurity.TransferBlstArmInverseFactorMagnitude01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSignedWordPrepare01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmCarryChains01 (sourceAddCarryChain)
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
open TransferBlstArmInverseWordNegation01 (sourceNegatedWordsAndCarry)
attribute [local irreducible] sourceAddCarryChain

/-! Source XOR-mask and add-one input preparation. The coded signed factor
determines the actual zero/all-ones mask. The negative branch's nonzero
input premise remains explicit until the original factor-row invariant is
instantiated. No compiled ASR/EOR/ADCS execution is asserted. -/

def sourceMaskPreparedWords (words : List UInt64) (mask : UInt64) : List UInt64 × Bool :=
  sourceAddCarryChain (decide ((mask >>> 63).toNat = 1))
    ((words.map (fun word => word ^^^ mask)).zip (List.replicate words.length (0 : UInt64)))

theorem every_source_mask_preparation_retains_the_entire_input_word_count
    (words : List UInt64) (mask : UInt64) : (sourceMaskPreparedWords words mask).1.length = words.length := by
  simp only [sourceMaskPreparedWords, TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
    List.length_zip, List.length_map, List.length_replicate, Nat.min_self]

theorem the_original_all_ones_mask_preparation_is_exactly_the_qualified_word_negation
    (words : List UInt64) : sourceMaskPreparedWords words (-1) = sourceNegatedWordsAndCarry words := by
  have carry : decide ((((-1 : UInt64) >>> 63).toNat) = 1) = true := by decide
  unfold sourceMaskPreparedWords
  rw [carry]
  simp only [UInt64.xor_neg_one]
  rfl

theorem the_original_zero_mask_preparation_is_exactly_the_zero_operand_carry_program
    (words : List UInt64) :
    sourceMaskPreparedWords words 0 = sourceAddCarryChain false (words.zip (List.replicate words.length (0 : UInt64))) := by
  have carry : decide ((((0 : UInt64) >>> 63).toNat) = 1) = false := by decide
  unfold sourceMaskPreparedWords
  rw [carry]
  simp only [UInt64.xor_zero, List.map_id_fun', id]

theorem the_original_zero_mask_preparation_has_clear_carry_and_the_entire_original_value
    (words : List UInt64) : (sourceMaskPreparedWords words 0).2 = false ∧
      packWords (sourceMaskPreparedWords words 0).1 = packWords words := by
  have zeroLength : (List.replicate words.length (0 : UInt64)).length = words.length := List.length_replicate
  have leftProjection : words.length ≤ (List.replicate words.length (0 : UInt64)).length := by rw [zeroLength]
  have rightProjection : (List.replicate words.length (0 : UInt64)).length ≤ words.length := by rw [zeroLength]
  have conserved := TransferBlstArmCarryChains01.symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    false (words.zip (List.replicate words.length (0 : UInt64)))
  rw [List.map_fst_zip leftProjection, List.map_snd_zip rightProjection, List.length_zip, zeroLength, Nat.min_self,
    TransferBlstArmInverseWordNegation01.any_number_of_zero_words_has_zero_entire_packed_value, Nat.add_zero] at conserved
  change packWords (sourceAddCarryChain false (words.zip (List.replicate words.length (0 : UInt64)))).1 +
    radix64 ^ words.length * (sourceAddCarryChain false (words.zip (List.replicate words.length (0 : UInt64)))).2.toNat = packWords words + 0 at conserved
  rw [Nat.add_zero] at conserved
  have bounded := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power words
  have result := TransferBlstArmInverseWordMultiplyOverflow01.an_exact_bounded_unsigned_carry_equation_forces_a_clear_flag_and_the_entire_value
    _ _ _ _ conserved bounded
  simpa only [the_original_zero_mask_preparation_is_exactly_the_zero_operand_carry_program] using result

theorem the_original_coded_factor_derives_its_entire_source_preparation_mask
    (factor : Int) (lower : -9223372036854775808 ≤ factor) (upper : factor < 9223372036854775808) :
    sourceFactorSignMask (sourceSignedWordCode factor) = if factor < 0 then (-1 : UInt64) else 0 := by
  simp only [TransferBlstArmInverseSignMask01.original_factor_arithmetic_shift_mask_is_the_exact_word_constant,
    TransferBlstArmInverseSignedWord01.original_unsigned_factor_sign_threshold_is_exact_integer_negativity factor lower upper]

theorem every_original_coded_factor_prepares_the_exact_unsigned_input_or_radix_complement
    (words : List UInt64) (factor : Int)
    (lower : -9223372036854775808 ≤ factor) (upper : factor < 9223372036854775808)
    (negativeNonzero : factor < 0 → 0 < packWords words) :
    (sourceMaskPreparedWords words (sourceFactorSignMask (sourceSignedWordCode factor))).2 = false ∧
      packWords (sourceMaskPreparedWords words (sourceFactorSignMask (sourceSignedWordCode factor))).1 =
        if factor < 0 then radix64 ^ words.length - packWords words else packWords words := by
  simp only [the_original_coded_factor_derives_its_entire_source_preparation_mask factor lower upper]
  by_cases negative : factor < 0
  · simp only [if_pos negative, the_original_all_ones_mask_preparation_is_exactly_the_qualified_word_negation]
    exact TransferBlstArmInverseWordNegation01.a_nonzero_entire_input_derives_zero_negation_carry_and_the_exact_radix_complement words (negativeNonzero negative)
  · simp only [if_neg negative]
    exact the_original_zero_mask_preparation_has_clear_carry_and_the_entire_original_value words

set_option pp.all true in
#check @sourceMaskPreparedWords
#print axioms sourceMaskPreparedWords
set_option pp.all true in
#check @every_source_mask_preparation_retains_the_entire_input_word_count
#print axioms every_source_mask_preparation_retains_the_entire_input_word_count
set_option pp.all true in
#check @the_original_all_ones_mask_preparation_is_exactly_the_qualified_word_negation
#print axioms the_original_all_ones_mask_preparation_is_exactly_the_qualified_word_negation
set_option pp.all true in
#check @the_original_zero_mask_preparation_is_exactly_the_zero_operand_carry_program
#print axioms the_original_zero_mask_preparation_is_exactly_the_zero_operand_carry_program
set_option pp.all true in
#check @the_original_zero_mask_preparation_has_clear_carry_and_the_entire_original_value
#print axioms the_original_zero_mask_preparation_has_clear_carry_and_the_entire_original_value
set_option pp.all true in
#check @the_original_coded_factor_derives_its_entire_source_preparation_mask
#print axioms the_original_coded_factor_derives_its_entire_source_preparation_mask
set_option pp.all true in
#check @every_original_coded_factor_prepares_the_exact_unsigned_input_or_radix_complement
#print axioms every_original_coded_factor_prepares_the_exact_unsigned_input_or_radix_complement
end ShielddSecurity.TransferBlstArmInverseSignedWordPrepare01
