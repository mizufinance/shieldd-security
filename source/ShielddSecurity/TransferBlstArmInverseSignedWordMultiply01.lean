import ShielddSecurity.TransferBlstArmInverseSignedTopOperand01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSignedWordMultiply01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
open TransferBlstArmInverseFactorMagnitude01 (sourceFactorMagnitudeWord)
open TransferBlstArmInverseSignedWordPrepare01 (sourceMaskPreparedWords)
open TransferBlstArmInverseSignedTopOperand01 (sourceFactorProductTopOffset)
open TransferBlstArmInverseWordMultiplyOffset01 (sourceOffsetWordMultiply)
attribute [local irreducible] sourceSignedWordCode sourceFactorSignMask sourceFactorMagnitudeWord
  sourceMaskPreparedWords sourceFactorProductTopOffset sourceOffsetWordMultiply

/-! Actual source sign-mask preparation, low/high products and AND/NEG top
operand compose to the full signed product modulo the extra output word.
The negative-nonzero condition remains explicit here. Original factor-row
instantiation, signed decoding, EXTR31 and compiled ISA remain separate. -/

theorem exact_sign_preparation_and_top_offset_reconstruct_the_entire_signed_product_residue
    (negative : Prop) [Decidable negative]
    (radix wordRadix input factor magnitude prepared operand : Int)
    (factorValue : factor = if negative then -magnitude else magnitude)
    (preparedValue : prepared = if negative then radix - input else input)
    (operandValue : operand = if negative then wordRadix - magnitude else 0) :
    (prepared * magnitude + radix * operand) % (radix * wordRadix) =
      (input * factor) % (radix * wordRadix) := by
  by_cases sign : negative
  · simp only [if_pos sign] at factorValue preparedValue operandValue
    rw [factorValue, preparedValue, operandValue]
    have algebra : (radix - input) * magnitude + radix * (wordRadix - magnitude) =
        input * (-magnitude) + radix * wordRadix := by ring1
    rw [algebra]
    exact Int.add_emod_right _ _
  · simp only [if_neg sign] at factorValue preparedValue operandValue
    rw [factorValue, preparedValue, operandValue, Int.mul_zero, Int.add_zero]

def sourceSignedMagnitudeProductWords (words : List UInt64) (factor : Int) : List UInt64 × Bool :=
  let factorWord := sourceSignedWordCode factor
  sourceOffsetWordMultiply (sourceMaskPreparedWords words (sourceFactorSignMask factorWord)).1
    (sourceFactorMagnitudeWord factorWord) (sourceFactorProductTopOffset factorWord)

theorem every_source_signed_magnitude_product_retains_exactly_one_extra_word
    (words : List UInt64) (factor : Int) :
    (sourceSignedMagnitudeProductWords words factor).1.length = words.length + 1 := by
  have count := TransferBlstArmInverseWordMultiplyOffset01.original_top_offset_product_retains_exactly_one_extra_word
    (sourceMaskPreparedWords words (sourceFactorSignMask (sourceSignedWordCode factor))).1
    (sourceFactorMagnitudeWord (sourceSignedWordCode factor)) (sourceFactorProductTopOffset (sourceSignedWordCode factor))
  rw [TransferBlstArmInverseSignedWordPrepare01.every_source_mask_preparation_retains_the_entire_input_word_count] at count
  exact count

theorem every_coded_signed_factor_is_its_entire_word_magnitude_with_the_original_sign
    (factor : Int) (lower : -9223372036854775808 ≤ factor) (upper : factor < 9223372036854775808) :
    factor = if factor < 0 then -((sourceFactorMagnitudeWord (sourceSignedWordCode factor)).toNat : Int)
      else ((sourceFactorMagnitudeWord (sourceSignedWordCode factor)).toNat : Int) := by
  have magnitude := TransferBlstArmInverseFactorMagnitude01.original_coded_signed_factor_asr_xor_subtract_recovers_integer_magnitude factor lower upper
  by_cases negative : factor < 0
  · rw [if_pos negative, magnitude]
    exact Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt negative)
  · rw [if_neg negative, magnitude]
    exact (Int.natAbs_of_nonneg (by omega : 0 ≤ factor)).symm

theorem every_coded_factor_prepares_the_entire_integer_input_or_radix_complement
    (words : List UInt64) (factor : Int)
    (lower : -9223372036854775808 ≤ factor) (upper : factor < 9223372036854775808)
    (negativeNonzero : factor < 0 → 0 < packWords words) :
    (packWords (sourceMaskPreparedWords words (sourceFactorSignMask (sourceSignedWordCode factor))).1 : Int) =
      if factor < 0 then ((radix64 ^ words.length : Nat) : Int) - (packWords words : Int) else (packWords words : Int) := by
  have prepared := (TransferBlstArmInverseSignedWordPrepare01.every_original_coded_factor_prepares_the_exact_unsigned_input_or_radix_complement
    words factor lower upper negativeNonzero).2
  have cast := congrArg (fun value : Nat => (value : Int)) prepared
  dsimp only at cast
  have bounded := Nat.le_of_lt (TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power words)
  by_cases negative : factor < 0
  · rw [if_pos negative, Nat.cast_sub bounded] at cast
    simpa only [if_pos negative] using cast
  · rw [if_neg negative] at cast
    simpa only [if_neg negative] using cast

theorem original_coded_factor_word_preparation_and_partial_products_derive_the_entire_signed_product_residue
    (words : List UInt64) (factor : Int)
    (lower : -9223372036854775808 ≤ factor) (upper : factor < 9223372036854775808)
    (negativeNonzero : factor < 0 → 0 < packWords words) :
    (packWords (sourceSignedMagnitudeProductWords words factor).1 : Int) % ((radix64 ^ (words.length + 1) : Nat) : Int) =
      ((packWords words : Int) * factor) % ((radix64 ^ (words.length + 1) : Nat) : Int) := by
  let prepared := (sourceMaskPreparedWords words (sourceFactorSignMask (sourceSignedWordCode factor))).1
  let magnitude := sourceFactorMagnitudeWord (sourceSignedWordCode factor)
  let operand := sourceFactorProductTopOffset (sourceSignedWordCode factor)
  have count : prepared.length = words.length :=
    TransferBlstArmInverseSignedWordPrepare01.every_source_mask_preparation_retains_the_entire_input_word_count _ _
  have observed := TransferBlstArmInverseWordMultiplyOffset01.original_top_offset_product_retains_the_entire_integer_residue_at_its_output_width
    prepared magnitude operand
  simp only [count] at observed
  have capacity : ((radix64 ^ (words.length + 1) : Nat) : Int) =
      ((radix64 ^ words.length : Nat) : Int) * (radix64 : Int) := by rw [Nat.pow_succ, Nat.cast_mul]
  have magnitudeValue := TransferBlstArmInverseFactorMagnitude01.original_coded_signed_factor_asr_xor_subtract_recovers_integer_magnitude factor lower upper
  have operandValue : (operand.toNat : Int) =
      if factor < 0 then (radix64 : Int) - (magnitude.toNat : Int) else 0 := by
    rw [magnitudeValue]
    exact TransferBlstArmInverseSignedTopOperand01.every_original_coded_factor_derives_the_entire_integer_top_offset_operand factor lower upper
  have recombined := exact_sign_preparation_and_top_offset_reconstruct_the_entire_signed_product_residue
    (factor < 0) ((radix64 ^ words.length : Nat) : Int) (radix64 : Int) (packWords words : Int) factor
    (magnitude.toNat : Int) (packWords prepared : Int) (operand.toNat : Int)
    (every_coded_signed_factor_is_its_entire_word_magnitude_with_the_original_sign factor lower upper)
    (every_coded_factor_prepares_the_entire_integer_input_or_radix_complement words factor lower upper negativeNonzero)
    operandValue
  have observedAtCapacity :
      (packWords (sourceSignedMagnitudeProductWords words factor).1 : Int) % (((radix64 ^ words.length : Nat) : Int) * (radix64 : Int)) =
        ((packWords prepared : Int) * (magnitude.toNat : Int) + ((radix64 ^ words.length : Nat) : Int) * (operand.toNat : Int)) %
          (((radix64 ^ words.length : Nat) : Int) * (radix64 : Int)) := by
    simpa only [capacity] using observed
  have combined := observedAtCapacity.trans recombined
  simpa only [←capacity] using combined

set_option pp.all true in
#check @exact_sign_preparation_and_top_offset_reconstruct_the_entire_signed_product_residue
#print axioms exact_sign_preparation_and_top_offset_reconstruct_the_entire_signed_product_residue
set_option pp.all true in
#check @sourceSignedMagnitudeProductWords
#print axioms sourceSignedMagnitudeProductWords
set_option pp.all true in
#check @every_source_signed_magnitude_product_retains_exactly_one_extra_word
#print axioms every_source_signed_magnitude_product_retains_exactly_one_extra_word
set_option pp.all true in
#check @every_coded_signed_factor_is_its_entire_word_magnitude_with_the_original_sign
#print axioms every_coded_signed_factor_is_its_entire_word_magnitude_with_the_original_sign
set_option pp.all true in
#check @every_coded_factor_prepares_the_entire_integer_input_or_radix_complement
#print axioms every_coded_factor_prepares_the_entire_integer_input_or_radix_complement
set_option pp.all true in
#check @original_coded_factor_word_preparation_and_partial_products_derive_the_entire_signed_product_residue
#print axioms original_coded_factor_word_preparation_and_partial_products_derive_the_entire_signed_product_residue
end ShielddSecurity.TransferBlstArmInverseSignedWordMultiply01
