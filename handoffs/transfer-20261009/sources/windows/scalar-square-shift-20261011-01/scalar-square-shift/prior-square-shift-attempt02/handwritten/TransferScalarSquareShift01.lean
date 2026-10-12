import ShielddSecurity.TransferScalarSquareCross01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarSquareShift01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSquareCross01 (sourceCrossWords crossValue)
/-! The source square doubles its cross terms with adjacent finite UInt64
left shifts, high-bit right shifts and OR. Exact disjoint low-bit arithmetic
and a symbolic word recurrence retain the top bit, producing eight words
with exactly twice the cross integer. Diagonal terms/final reduction and
native primitive/compiler/caller correspondence remain separate. -/

def sourceDoubleAdjacent (word previous : UInt64) : UInt64 :=
  (word <<< 1) ||| (previous >>> 63)

def sourceDoubleWalk (previous : UInt64) : List UInt64 → List UInt64
  | [] => [previous >>> 63]
  | word :: rest => sourceDoubleAdjacent word previous :: sourceDoubleWalk word rest

theorem source_high_shift_is_exact_zero_or_one_integer_bit (word : UInt64) :
    (word >>> 63).toNat = word.toNat / 2 ^ 63 ∧ (word >>> 63).toNat < 2 := by
  have value : (word >>> 63).toNat = word.toNat / 2 ^ 63 := by
    rw [UInt64.toNat_shiftRight]
    change word.toNat >>> 63 = word.toNat / 2 ^ 63
    exact Nat.shiftRight_eq_div_pow _ _
  refine ⟨value, ?_⟩
  rw [value]
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 63)).mpr word.toNat_lt

theorem source_adjacent_shift_or_is_exact_disjoint_low_sum (word previous : UInt64) :
    (sourceDoubleAdjacent word previous).toNat =
      (2 * word.toNat) % radix64 + previous.toNat / 2 ^ 63 := by
  rw [sourceDoubleAdjacent, UInt64.toNat_or, UInt64.toNat_shiftLeft,
    (source_high_shift_is_exact_zero_or_one_integer_bit previous).1]
  change ((word.toNat <<< 1) % radix64) ||| (previous.toNat / 2 ^ 63) = _
  rw [Nat.shiftLeft_eq]
  change (word.toNat * 2 % radix64) ||| (previous.toNat / 2 ^ 63) = _
  have factor : radix64 = 2 * 2 ^ 63 := by decide
  rw [Nat.mul_comm word.toNat 2, factor, Nat.mul_mod_mul_left]
  have bitBound : previous.toNat / 2 ^ 63 < 2 ^ 1 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 63)).mpr previous.toNat_lt
  have disjoint := Nat.shiftLeft_add_eq_or_of_lt bitBound (word.toNat % 2 ^ 63)
  rw [Nat.shiftLeft_eq] at disjoint
  change (word.toNat % 2 ^ 63) * 2 + previous.toNat / 2 ^ 63 =
    ((word.toNat % 2 ^ 63) * 2) ||| (previous.toNat / 2 ^ 63) at disjoint
  rw [Nat.mul_comm (word.toNat % 2 ^ 63) 2] at disjoint
  exact disjoint.symm

theorem source_adjacent_shift_and_high_bit_conserve_full_doubled_word (word previous : UInt64) :
    (sourceDoubleAdjacent word previous).toNat + radix64 * (word >>> 63).toNat =
      2 * word.toNat + (previous >>> 63).toNat := by
  rw [source_adjacent_shift_or_is_exact_disjoint_low_sum,
    (source_high_shift_is_exact_zero_or_one_integer_bit word).1,
    (source_high_shift_is_exact_zero_or_one_integer_bit previous).1]
  have factor : radix64 = 2 * 2 ^ 63 := by decide
  have split := Nat.mod_add_div word.toNat (2 ^ 63)
  have full : (2 * word.toNat) % radix64 + radix64 * (word.toNat / 2 ^ 63) = 2 * word.toNat := by
    rw [factor, Nat.mul_mod_mul_left]
    calc
      _ = 2 * (word.toNat % 2 ^ 63 + 2 ^ 63 * (word.toNat / 2 ^ 63)) := by rw [Nat.mul_add]; ac_rfl
      _ = _ := by rw [split]
  calc
    _ = ((2 * word.toNat) % radix64 + radix64 * (word.toNat / 2 ^ 63)) + previous.toNat / 2 ^ 63 := by ac_rfl
    _ = _ := by rw [full]

theorem symbolic_source_double_walk_retains_top_bit_and_exact_integer (previous : UInt64) (words : List UInt64) :
    (sourceDoubleWalk previous words).length = words.length + 1 ∧
      packWords (sourceDoubleWalk previous words) = 2 * packWords words + (previous >>> 63).toNat := by
  induction words generalizing previous with
  | nil =>
    constructor
    · rfl
    · change (previous >>> 63).toNat + radix64 * 0 = 2 * 0 + (previous >>> 63).toNat
      simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  | cons word rest ih =>
    have tail := ih word
    have first := source_adjacent_shift_and_high_bit_conserve_full_doubled_word word previous
    constructor
    · change (sourceDoubleWalk word rest).length + 1 = (rest.length + 1) + 1
      rw [tail.1]
    · change (sourceDoubleAdjacent word previous).toNat + radix64 * packWords (sourceDoubleWalk word rest) =
        2 * (word.toNat + radix64 * packWords rest) + (previous >>> 63).toNat
      rw [tail.2]
      calc
        _ = ((sourceDoubleAdjacent word previous).toNat + radix64 * (word >>> 63).toNat) + 2 * (radix64 * packWords rest) := by rw [Nat.mul_add]; ac_rfl
        _ = (2 * word.toNat + (previous >>> 63).toNat) + 2 * (radix64 * packWords rest) := by rw [first]
        _ = _ := by rw [Nat.mul_add]; ac_rfl

theorem source_seven_word_cross_shift_retains_eight_words_and_exact_doubled_cross (self : Vector UInt64 4) :
    (sourceDoubleWalk 0 (sourceCrossWords self)).length = 8 ∧
      packWords (sourceDoubleWalk 0 (sourceCrossWords self)) = 2 * (radix64 * crossValue self.toList) := by
  have prefix := TransferScalarSquareCross01.source_six_cross_mac_prefix_derives_seven_words_and_exact_cross_integer self
  have doubled := symbolic_source_double_walk_retains_top_bit_and_exact_integer 0 (sourceCrossWords self)
  have zero : ((0 : UInt64) >>> 63).toNat = 0 := rfl
  rw [prefix.1, prefix.2, zero, Nat.add_zero] at doubled
  exact doubled

set_option pp.all true in
#check @sourceDoubleAdjacent
#print axioms sourceDoubleAdjacent
set_option pp.all true in
#check @sourceDoubleWalk
#print axioms sourceDoubleWalk
set_option pp.all true in
#check @source_high_shift_is_exact_zero_or_one_integer_bit
#print axioms source_high_shift_is_exact_zero_or_one_integer_bit
set_option pp.all true in
#check @source_adjacent_shift_or_is_exact_disjoint_low_sum
#print axioms source_adjacent_shift_or_is_exact_disjoint_low_sum
set_option pp.all true in
#check @source_adjacent_shift_and_high_bit_conserve_full_doubled_word
#print axioms source_adjacent_shift_and_high_bit_conserve_full_doubled_word
set_option pp.all true in
#check @symbolic_source_double_walk_retains_top_bit_and_exact_integer
#print axioms symbolic_source_double_walk_retains_top_bit_and_exact_integer
set_option pp.all true in
#check @source_seven_word_cross_shift_retains_eight_words_and_exact_doubled_cross
#print axioms source_seven_word_cross_shift_retains_eight_words_and_exact_doubled_cross
end ShielddSecurity.TransferScalarSquareShift01
