import ShielddSecurity.TransferBlstArmInverseWordNegation01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordMultiply01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmCarryChains01 (sourceAddCarryChain)

/-! Word-level low/high partial products and their shifted carry sum.
UInt64 multiplication supplies MUL semantics; the defined high quotient
supplies the UMULH arithmetic model. No compiled-instruction execution,
pointer/load correspondence, or signed high-offset conclusion is assumed. -/

def sourceMultiplyWordLow (word multiplier : UInt64) : UInt64 := word * multiplier
def sourceMultiplyWordHigh (word multiplier : UInt64) : UInt64 :=
  UInt64.ofNat (word.toNat * multiplier.toNat / radix64)

theorem every_full_two_word_product_is_strictly_below_the_double_radix
    (word multiplier : UInt64) : word.toNat * multiplier.toNat < radix64 * radix64 := by
  have wordBound : word.toNat < radix64 := word.toNat_lt
  have multiplierBound : multiplier.toNat < radix64 := multiplier.toNat_lt
  have positive : 0 < radix64 := by decide
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right multiplier.toNat (Nat.le_of_lt wordBound))
    (Nat.mul_lt_mul_of_pos_left multiplierBound positive)

theorem original_low_and_high_word_products_conserve_the_entire_unsigned_product
    (word multiplier : UInt64) :
    (sourceMultiplyWordLow word multiplier).toNat + radix64 * (sourceMultiplyWordHigh word multiplier).toNat =
      word.toNat * multiplier.toNat := by
  have positive : 0 < radix64 := by decide
  have highBound : word.toNat * multiplier.toNat / radix64 < radix64 :=
    (Nat.div_lt_iff_lt_mul positive).mpr (every_full_two_word_product_is_strictly_below_the_double_radix word multiplier)
  have high : (sourceMultiplyWordHigh word multiplier).toNat = word.toNat * multiplier.toNat / radix64 := by
    exact UInt64.toNat_ofNat_of_lt' highBound
  have low : (sourceMultiplyWordLow word multiplier).toNat = word.toNat * multiplier.toNat % radix64 :=
    UInt64.toNat_mul word multiplier
  rw [high, low]
  exact Nat.mod_add_div _ _

attribute [local irreducible] sourceMultiplyWordLow sourceMultiplyWordHigh

theorem symbolic_low_and_high_partial_product_lists_conserve_the_entire_packed_product
    (words : List UInt64) (multiplier : UInt64) :
    packWords (words.map (fun word => sourceMultiplyWordLow word multiplier)) +
      radix64 * packWords (words.map (fun word => sourceMultiplyWordHigh word multiplier)) =
      packWords words * multiplier.toNat := by
  induction words with
  | nil => simp only [List.map_nil, packWords, Nat.mul_zero, Nat.zero_add, Nat.zero_mul]
  | cons word rest ih =>
    change ((sourceMultiplyWordLow word multiplier).toNat + radix64 * packWords (rest.map (fun w => sourceMultiplyWordLow w multiplier))) +
      radix64 * ((sourceMultiplyWordHigh word multiplier).toNat + radix64 * packWords (rest.map (fun w => sourceMultiplyWordHigh w multiplier))) =
        (word.toNat + radix64 * packWords rest) * multiplier.toNat
    calc
      _ = ((sourceMultiplyWordLow word multiplier).toNat + radix64 * (sourceMultiplyWordHigh word multiplier).toNat) +
          radix64 * (packWords (rest.map (fun w => sourceMultiplyWordLow w multiplier)) +
            radix64 * packWords (rest.map (fun w => sourceMultiplyWordHigh w multiplier))) := by ring1
      _ = word.toNat * multiplier.toNat + radix64 * (packWords rest * multiplier.toNat) := by
        rw [original_low_and_high_word_products_conserve_the_entire_unsigned_product, ih]
      _ = _ := by ring1

set_option pp.all true in
#check @sourceMultiplyWordLow
#print axioms sourceMultiplyWordLow
set_option pp.all true in
#check @sourceMultiplyWordHigh
#print axioms sourceMultiplyWordHigh
set_option pp.all true in
#check @every_full_two_word_product_is_strictly_below_the_double_radix
#print axioms every_full_two_word_product_is_strictly_below_the_double_radix
set_option pp.all true in
#check @original_low_and_high_word_products_conserve_the_entire_unsigned_product
#print axioms original_low_and_high_word_products_conserve_the_entire_unsigned_product
set_option pp.all true in
#check @symbolic_low_and_high_partial_product_lists_conserve_the_entire_packed_product
#print axioms symbolic_low_and_high_partial_product_lists_conserve_the_entire_packed_product
end ShielddSecurity.TransferBlstArmInverseWordMultiply01
