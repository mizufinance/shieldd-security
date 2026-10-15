import ShielddSecurity.TransferBlstArmInverseTopFixup01
import ShielddSecurity.TransferBlstArmInverseFirst01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseCoefficientEncoding01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseSign01 (sourceWideRadix)
open TransferBlstArmInverseFirst01 (WideState sourceWideRaw sourceWideMeaning)
open TransferBlstArmInverseWordRepack01 (sourceFourWordsOfNat)

/-! An explicit full coefficient encoding into the original low/high/top
source state. Encoding correctness supplies no theorem that the native
multiply/carry producer constructs this state. -/

def sourceCoefficientFourWordVector (input : Nat) : Vector UInt64 4 :=
  let words := sourceFourWordsOfNat input
  #v[words.w0, words.w1, words.w2, words.w3]

theorem four_coefficient_encoding_words_pack_to_the_original_four_word_repacking
    (input : Nat) :
    packWords (sourceCoefficientFourWordVector input).toList =
      TransferBlstArmInverseWindowSelect01.sourcePackedFourWords (sourceFourWordsOfNat input) := by
  rfl

def sourceCoefficientWideState (value : Int) : WideState :=
  let raw := (value % sourceWideRadix).toNat
  (sourceCoefficientFourWordVector (raw % (radix64 ^ 4)),
    sourceCoefficientFourWordVector (raw / (radix64 ^ 4)), value / sourceWideRadix)

theorem every_integer_coefficient_has_a_nonnegative_strictly_bounded_unsigned_raw_part
    (value : Int) :
    0 ≤ value % sourceWideRadix ∧ value % sourceWideRadix < sourceWideRadix := by
  have positive : 0 < sourceWideRadix := by decide
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ positive⟩

theorem every_integer_coefficient_unsigned_raw_part_fits_the_two_original_four_word_halves
    (value : Int) : (value % sourceWideRadix).toNat < (radix64 ^ 4) * (radix64 ^ 4) := by
  have range := every_integer_coefficient_has_a_nonnegative_strictly_bounded_unsigned_raw_part value
  have castBound : ((value % sourceWideRadix).toNat : Int) < sourceWideRadix := by
    rw [Int.toNat_of_nonneg range.1]
    exact range.2
  have radix : sourceWideRadix = (((radix64 ^ 4) * (radix64 ^ 4) : Nat) : Int) := by decide
  have finalBound : ((value % sourceWideRadix).toNat : Int) < (((radix64 ^ 4) * (radix64 ^ 4) : Nat) : Int) :=
    castBound.trans_eq radix
  exact_mod_cast finalBound

theorem every_integer_coefficient_encoding_has_the_entire_original_unsigned_raw_value
    (value : Int) : sourceWideRaw (sourceCoefficientWideState value) = (value % sourceWideRadix).toNat := by
  let raw := (value % sourceWideRadix).toNat
  have bound := every_integer_coefficient_unsigned_raw_part_fits_the_two_original_four_word_halves value
  have positive : 0 < radix64 ^ 4 := by decide
  have lowBound : raw % (radix64 ^ 4) < radix64 ^ 4 := Nat.mod_lt raw positive
  have highBound : raw / (radix64 ^ 4) < radix64 ^ 4 := (Nat.div_lt_iff_lt_mul positive).mpr bound
  have capacity : radix64 ^ 4 = 2 ^ 256 := by decide
  have low := TransferBlstArmInverseWordRepack01.original_four_word_repacking_reconstructs_every_input_below_two256
    (raw % (radix64 ^ 4)) (by rw [←capacity]; exact lowBound)
  have high := TransferBlstArmInverseWordRepack01.original_four_word_repacking_reconstructs_every_input_below_two256
    (raw / (radix64 ^ 4)) (by rw [←capacity]; exact highBound)
  dsimp only [sourceWideRaw, sourceCoefficientWideState]
  rw [TransferBlstArmInverseFirst01.symbolic_word_append_has_the_entire_radix_weighted_value,
    Vector.length_toList, four_coefficient_encoding_words_pack_to_the_original_four_word_repacking,
    four_coefficient_encoding_words_pack_to_the_original_four_word_repacking, low, high]
  exact Nat.mod_add_div raw (radix64 ^ 4)

theorem every_integer_coefficient_encoding_has_the_entire_original_signed_wide_meaning
    (value : Int) : sourceWideMeaning (sourceCoefficientWideState value) = value := by
  have range := every_integer_coefficient_has_a_nonnegative_strictly_bounded_unsigned_raw_part value
  rw [sourceWideMeaning, every_integer_coefficient_encoding_has_the_entire_original_unsigned_raw_value,
    Int.toNat_of_nonneg range.1]
  exact Int.emod_add_mul_ediv value sourceWideRadix

set_option pp.all true in
#check @sourceCoefficientFourWordVector
#print axioms sourceCoefficientFourWordVector
set_option pp.all true in
#check @four_coefficient_encoding_words_pack_to_the_original_four_word_repacking
#print axioms four_coefficient_encoding_words_pack_to_the_original_four_word_repacking
set_option pp.all true in
#check @sourceCoefficientWideState
#print axioms sourceCoefficientWideState
set_option pp.all true in
#check @every_integer_coefficient_has_a_nonnegative_strictly_bounded_unsigned_raw_part
#print axioms every_integer_coefficient_has_a_nonnegative_strictly_bounded_unsigned_raw_part
set_option pp.all true in
#check @every_integer_coefficient_unsigned_raw_part_fits_the_two_original_four_word_halves
#print axioms every_integer_coefficient_unsigned_raw_part_fits_the_two_original_four_word_halves
set_option pp.all true in
#check @every_integer_coefficient_encoding_has_the_entire_original_unsigned_raw_value
#print axioms every_integer_coefficient_encoding_has_the_entire_original_unsigned_raw_value
set_option pp.all true in
#check @every_integer_coefficient_encoding_has_the_entire_original_signed_wide_meaning
#print axioms every_integer_coefficient_encoding_has_the_entire_original_signed_wide_meaning
end ShielddSecurity.TransferBlstArmInverseCoefficientEncoding01
