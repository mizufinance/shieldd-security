import ShielddSecurity.TransferScalarPowInvariant01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarConstantEquality01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferScalarPowInvariant01 (sourceZero)
/-! Source-shaped locked subtle2.6.1 unsigned64 equality is XOR, wrapping
negation, OR, high-bit shift and XOR1/cast. Scalar ANDs four such bytes;
invert negates that Choice. Every equality/refusal byte value is derived.
Compiler/volatile optimization barrier/caller origin/timing is separate. -/

theorem exact_word_or_wrapping_negation_high_bit_detects_nonzero (word : UInt64) :
    ((word ||| (-word)) >>> 63) = if word = 0 then 0 else 1 := by
  by_cases zero : word = 0
  · rw [zero] <;> rfl
  · have bounded : word.toNat < 18446744073709551616 := word.toNat_lt
    have positive : 0 < word.toNat := by
      have nonzero : word.toNat ≠ 0 := by
        intro impossible
        exact zero (UInt64.toNat_inj.mp impossible)
      omega
    have negated : (-word).toNat = 18446744073709551616 - word.toNat := by
      rw [UInt64.toNat_neg]
      change (18446744073709551616 - word.toNat) % 18446744073709551616 = _
      rw [Nat.mod_eq_of_lt (by omega)]
    have dominatesLeft : word.toNat ≤ (word ||| (-word)).toNat := by
      rw [UInt64.toNat_or]
      exact Nat.left_le_or
    have dominatesRight : (-word).toNat ≤ (word ||| (-word)).toNat := by
      rw [UInt64.toNat_or]
      exact Nat.right_le_or
    have high : 9223372036854775808 ≤ (word ||| (-word)).toNat := by
      by_cases low : word.toNat < 9223372036854775808
      · rw [negated] at dominatesRight
        omega
      · omega
    have upper : (word ||| (-word)).toNat < 18446744073709551616 := (word ||| (-word)).toNat_lt
    rw [if_neg zero]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    change (word ||| (-word)).toNat / 9223372036854775808 = 1
    exact Nat.div_eq_of_lt_le (by omega) (by omega)

def sourceWordCtEqByte (a b : UInt64) : UInt8 :=
  UInt8.ofNat ((((a ^^^ b) ||| (-(a ^^^ b))) >>> 63) ^^^ 1).toNat

theorem exact_source_unsigned_word_equality_byte_is_the_equality_boolean (a b : UInt64) :
    sourceWordCtEqByte a b = if a == b then 1 else 0 := by
  rw [sourceWordCtEqByte, exact_word_or_wrapping_negation_high_bit_detects_nonzero]
  by_cases same : a = b
  · simp [UInt64.xor_eq_zero_iff, same]
  · simp [UInt64.xor_eq_zero_iff, same]

theorem source_boolean_choice_byte_and_has_the_exact_boolean_value (first second : Bool) :
    ((if first then 1 else 0 : UInt8) &&& (if second then 1 else 0 : UInt8)) =
      if first && second then 1 else 0 := by
  cases first <;> cases second <;> rfl

theorem exact_four_word_vector_equality_is_all_four_component_equalities
    (a b : Vector UInt64 4) :
    a = b ↔ a[0] = b[0] ∧ a[1] = b[1] ∧ a[2] = b[2] ∧ a[3] = b[3] := by
  constructor
  · intro same
    subst b
    exact ⟨rfl,rfl,rfl,rfl⟩
  · intro same
    apply Vector.ext
    intro i bounded
    have positions : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases positions with rfl | rfl | rfl | rfl
    · exact same.1
    · exact same.2.1
    · exact same.2.2.1
    · exact same.2.2.2

def sourceScalarWordsCtEqByte (a b : Vector UInt64 4) : UInt8 :=
  sourceWordCtEqByte a[0] b[0] &&& sourceWordCtEqByte a[1] b[1] &&&
    sourceWordCtEqByte a[2] b[2] &&& sourceWordCtEqByte a[3] b[3]

theorem exact_source_scalar_equality_byte_derives_exact_raw_word_equality
    (a b : Vector UInt64 4) : sourceScalarWordsCtEqByte a b = if a = b then 1 else 0 := by
  simp only [sourceScalarWordsCtEqByte, exact_source_unsigned_word_equality_byte_is_the_equality_boolean]
  rw [source_boolean_choice_byte_and_has_the_exact_boolean_value,
    source_boolean_choice_byte_and_has_the_exact_boolean_value,
    source_boolean_choice_byte_and_has_the_exact_boolean_value]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  rw [← exact_four_word_vector_equality_is_all_four_component_equalities]

theorem exact_source_scalar_equality_byte_has_derived_zero_one_invariant
    (a b : Vector UInt64 4) : (sourceScalarWordsCtEqByte a b).toNat < 2 := by
  rw [exact_source_scalar_equality_byte_derives_exact_raw_word_equality]
  split <;> decide

def sourceNotChoiceByte (byte : UInt8) : UInt8 :=
  1 &&& (~~~byte)

def sourceInvertFlagByte (self : CanonicalScalar) : UInt8 :=
  sourceNotChoiceByte (sourceScalarWordsCtEqByte self.words sourceZero.words)

theorem exact_source_invert_choice_flag_is_refusal_at_mathematical_zero
    (self : CanonicalScalar) :
    sourceInvertFlagByte self = if montgomeryValue self.words = 0 then 0 else 1 := by
  have corresponds := TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal self sourceZero
  rw [TransferScalarPowInvariant01.source_zero_and_one_constants_have_exact_canonical_montgomery_keys.1] at corresponds
  rw [sourceInvertFlagByte, exact_source_scalar_equality_byte_derives_exact_raw_word_equality]
  by_cases zero : self.words = sourceZero.words
  · have keyZero := corresponds.mpr zero
    rw [if_pos zero, if_pos keyZero, sourceNotChoiceByte] <;> rfl
  · have keyNonzero : montgomeryValue self.words ≠ 0 := by
      intro impossible
      exact zero (corresponds.mp impossible)
    rw [if_neg zero, if_neg keyNonzero, sourceNotChoiceByte] <;> rfl

theorem exact_source_invert_choice_flag_has_derived_zero_one_invariant
    (self : CanonicalScalar) : (sourceInvertFlagByte self).toNat < 2 := by
  rw [exact_source_invert_choice_flag_is_refusal_at_mathematical_zero]
  split <;> decide

set_option pp.all true in
#check @exact_word_or_wrapping_negation_high_bit_detects_nonzero
#print axioms exact_word_or_wrapping_negation_high_bit_detects_nonzero
set_option pp.all true in
#check @sourceWordCtEqByte
#print axioms sourceWordCtEqByte
set_option pp.all true in
#check @exact_source_unsigned_word_equality_byte_is_the_equality_boolean
#print axioms exact_source_unsigned_word_equality_byte_is_the_equality_boolean
set_option pp.all true in
#check @source_boolean_choice_byte_and_has_the_exact_boolean_value
#print axioms source_boolean_choice_byte_and_has_the_exact_boolean_value
set_option pp.all true in
#check @exact_four_word_vector_equality_is_all_four_component_equalities
#print axioms exact_four_word_vector_equality_is_all_four_component_equalities
set_option pp.all true in
#check @sourceScalarWordsCtEqByte
#print axioms sourceScalarWordsCtEqByte
set_option pp.all true in
#check @exact_source_scalar_equality_byte_derives_exact_raw_word_equality
#print axioms exact_source_scalar_equality_byte_derives_exact_raw_word_equality
set_option pp.all true in
#check @exact_source_scalar_equality_byte_has_derived_zero_one_invariant
#print axioms exact_source_scalar_equality_byte_has_derived_zero_one_invariant
set_option pp.all true in
#check @sourceNotChoiceByte
#print axioms sourceNotChoiceByte
set_option pp.all true in
#check @sourceInvertFlagByte
#print axioms sourceInvertFlagByte
set_option pp.all true in
#check @exact_source_invert_choice_flag_is_refusal_at_mathematical_zero
#print axioms exact_source_invert_choice_flag_is_refusal_at_mathematical_zero
set_option pp.all true in
#check @exact_source_invert_choice_flag_has_derived_zero_one_invariant
#print axioms exact_source_invert_choice_flag_has_derived_zero_one_invariant
end ShielddSecurity.TransferScalarConstantEquality01
