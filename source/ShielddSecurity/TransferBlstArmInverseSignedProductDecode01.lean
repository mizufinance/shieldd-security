import ShielddSecurity.TransferBlstArmInverseSignedWordMultiply01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSignedProductDecode01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseSignedWordMultiply01 (sourceSignedMagnitudeProductWords)
attribute [local irreducible] sourceSignedMagnitudeProductWords

/-! Recover the full signed product from its output-width residue and
derived signed64/input/output bounds. The decoder is an integer model;
top-word ASR correspondence, sum/EXTR31 and compiled ISA remain separate. -/

def sourceSignedRadixDecode (half unsigned : Int) : Int :=
  if half ≤ unsigned then unsigned - 2 * half else unsigned

theorem exact_residue_and_both_entire_ranges_derive_the_full_signed_integer
    (half unsigned value : Int)
    (unsignedNonnegative : 0 ≤ unsigned) (unsignedSmall : unsigned < 2 * half)
    (signedLower : -half ≤ value) (signedUpper : value < half)
    (residue : unsigned % (2 * half) = value % (2 * half)) :
    sourceSignedRadixDecode half unsigned = value := by
  have unsignedReduced := Int.emod_eq_of_lt unsignedNonnegative unsignedSmall
  by_cases nonnegative : 0 ≤ value
  · have valueSmall : value < 2 * half := by omega
    rw [unsignedReduced, Int.emod_eq_of_lt nonnegative valueSmall] at residue
    have noSign : ¬half ≤ unsigned := by omega
    rw [sourceSignedRadixDecode, if_neg noSign]
    exact residue
  · have shiftedNonnegative : 0 ≤ value + 2 * half := by omega
    have shiftedSmall : value + 2 * half < 2 * half := by omega
    have period := Int.add_emod_right value (2 * half)
    rw [Int.emod_eq_of_lt shiftedNonnegative shiftedSmall] at period
    rw [unsignedReduced, ←period] at residue
    have sign : half ≤ unsigned := by omega
    rw [sourceSignedRadixDecode, if_pos sign]
    omega

theorem every_signed64_factor_has_magnitude_at_most_the_unsigned_half_word
    (factor : Int) (lower : -9223372036854775808 ≤ factor) (upper : factor < 9223372036854775808) :
    factor.natAbs ≤ 9223372036854775808 := by
  have castBound : (factor.natAbs : Int) ≤ 9223372036854775808 := by
    by_cases nonnegative : 0 ≤ factor
    · rw [Int.natAbs_of_nonneg nonnegative]
      omega
    · have signed := Int.eq_neg_natAbs_of_nonpos (by omega : factor ≤ 0)
      omega
  exact_mod_cast castBound

theorem every_unsigned_word_input_times_signed64_factor_fits_strictly_inside_the_full_signed_output_range
    (words : List UInt64) (factor : Int)
    (lower : -9223372036854775808 ≤ factor) (upper : factor < 9223372036854775808) :
    ((packWords words : Int) * factor).natAbs < radix64 ^ words.length * 9223372036854775808 := by
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  have packed := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power words
  have magnitude := every_signed64_factor_has_magnitude_at_most_the_unsigned_half_word factor lower upper
  have weak := Nat.mul_le_mul_left (packWords words) magnitude
  have strong := Nat.mul_lt_mul_of_pos_right packed (by decide : 0 < 9223372036854775808)
  exact Nat.lt_of_le_of_lt weak strong

theorem the_extra_output_word_capacity_is_exactly_twice_the_entire_signed_half_capacity
    (count : Nat) : radix64 ^ (count + 1) = 2 * (radix64 ^ count * 9223372036854775808) := by
  have radix : radix64 = 2 * 9223372036854775808 := by decide
  calc
    _ = radix64 ^ count * radix64 := Nat.pow_succ _ _
    _ = radix64 ^ count * (2 * 9223372036854775808) := by rw [radix]
    _ = _ := by ring1

theorem original_coded_factor_partial_products_derive_the_entire_signed_integer_product
    (words : List UInt64) (factor : Int)
    (lower : -9223372036854775808 ≤ factor) (upper : factor < 9223372036854775808)
    (negativeNonzero : factor < 0 → 0 < packWords words) :
    sourceSignedRadixDecode ((radix64 ^ words.length * 9223372036854775808 : Nat) : Int)
      (packWords (sourceSignedMagnitudeProductWords words factor).1 : Int) = (packWords words : Int) * factor := by
  let half := radix64 ^ words.length * 9223372036854775808
  have capacity : ((radix64 ^ (words.length + 1) : Nat) : Int) = 2 * (half : Int) := by
    have cast := congrArg (fun value : Nat => (value : Int))
      (the_extra_output_word_capacity_is_exactly_twice_the_entire_signed_half_capacity words.length)
    dsimp only at cast
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using cast
  have absolute := every_unsigned_word_input_times_signed64_factor_fits_strictly_inside_the_full_signed_output_range words factor lower upper
  have absoluteCast : ((((packWords words : Int) * factor).natAbs : Nat) : Int) < (half : Int) := by exact_mod_cast absolute
  have upperValue := Int.le_natAbs (a := (packWords words : Int) * factor)
  have lowerValue := Int.le_natAbs (a := -((packWords words : Int) * factor))
  rw [Int.natAbs_neg] at lowerValue
  have signedLower : -(half : Int) ≤ (packWords words : Int) * factor := by omega
  have signedUpper : (packWords words : Int) * factor < (half : Int) := by omega
  have unsignedBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (sourceSignedMagnitudeProductWords words factor).1
  rw [TransferBlstArmInverseSignedWordMultiply01.every_source_signed_magnitude_product_retains_exactly_one_extra_word] at unsignedBound
  have unsignedSmall : (packWords (sourceSignedMagnitudeProductWords words factor).1 : Int) <
      ((radix64 ^ (words.length + 1) : Nat) : Int) := by exact_mod_cast unsignedBound
  rw [capacity] at unsignedSmall
  have residue := TransferBlstArmInverseSignedWordMultiply01.original_coded_factor_word_preparation_and_partial_products_derive_the_entire_signed_product_residue
    words factor lower upper negativeNonzero
  rw [capacity] at residue
  exact exact_residue_and_both_entire_ranges_derive_the_full_signed_integer
    (half : Int) (packWords (sourceSignedMagnitudeProductWords words factor).1 : Int) ((packWords words : Int) * factor)
    (Int.natCast_nonneg _) unsignedSmall signedLower signedUpper residue

set_option pp.all true in
#check @sourceSignedRadixDecode
#print axioms sourceSignedRadixDecode
set_option pp.all true in
#check @exact_residue_and_both_entire_ranges_derive_the_full_signed_integer
#print axioms exact_residue_and_both_entire_ranges_derive_the_full_signed_integer
set_option pp.all true in
#check @every_signed64_factor_has_magnitude_at_most_the_unsigned_half_word
#print axioms every_signed64_factor_has_magnitude_at_most_the_unsigned_half_word
set_option pp.all true in
#check @every_unsigned_word_input_times_signed64_factor_fits_strictly_inside_the_full_signed_output_range
#print axioms every_unsigned_word_input_times_signed64_factor_fits_strictly_inside_the_full_signed_output_range
set_option pp.all true in
#check @the_extra_output_word_capacity_is_exactly_twice_the_entire_signed_half_capacity
#print axioms the_extra_output_word_capacity_is_exactly_twice_the_entire_signed_half_capacity
set_option pp.all true in
#check @original_coded_factor_partial_products_derive_the_entire_signed_integer_product
#print axioms original_coded_factor_partial_products_derive_the_entire_signed_integer_product
end ShielddSecurity.TransferBlstArmInverseSignedProductDecode01
