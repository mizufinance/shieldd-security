import ShielddSecurity.TransferScalarWideWalk01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarWideReduction01
open TransferScalarSerializationRange01 (radix64 normalize)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarWideWalk01 (wideRounds)
open TransferScalarWideRound01 (wideValue)
open TransferScalarWideProduct01 (sourceWideProduct)
open TransferScalarMaskedNormalization01 (sourceNormalize)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Source-shaped wide reduction performs four MAC/ADC rounds, discards the
final deferred carry and uses the exact sub/borrow-masked addback. The input
range derives zero discarded carry and canonical output, rather than assuming
them. Canonical right operand gives the schoolbook product range. Native
private Scalar invariant, compiler/primitive/full trace and R2 remain separate. -/

def sourceWideReduce (words : List UInt64) : List UInt64 :=
  sourceNormalize (wideRounds 4 (words, 0)).1

def sourceMulMontgomery (self rhs : Vector UInt64 4) : List UInt64 :=
  sourceWideReduce (sourceWideProduct self rhs)

theorem twice_actual_modulus_fits_four_word_radix :
    2 * nullifierModulus < radix64 ^ 4 := by decide

theorem canonical_right_operand_derives_full_product_range
    (self rhs : Vector UInt64 4) (canonical : packWords rhs.toList < nullifierModulus) :
    packWords (sourceWideProduct self rhs) < nullifierModulus * radix64 ^ 4 := by
  have product := TransferScalarWideProduct01.source_schoolbook_product_has_exact_eight_limbs_value_and_range self rhs
  have selfBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power self.toList
  rw [Vector.length_toList] at selfBound
  have bounded := Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt selfBound) canonical (by decide : 0 < radix64 ^ 4)
  rw [product.2.1]
  simpa only [Nat.mul_comm] using bounded

theorem four_wide_rounds_derive_zero_discarded_carry_and_bounded_low_words
    (words : List UInt64) (eight : words.length = 8)
    (bound : packWords words < nullifierModulus * (radix64 ^ 4 + 1)) :
    (wideRounds 4 (words, 0)).1.length = 4 ∧ (wideRounds 4 (words, 0)).2 = 0 ∧
      packWords (wideRounds 4 (words, 0)).1 < 2 * nullifierModulus := by
  have initialWidth : (words, (0 : UInt64)).1.length = 4 + 4 := eight
  have initialBound : wideValue (words, 0) < nullifierModulus * (radix64 ^ 4 + 1) := by
    simpa only [wideValue, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] using bound
  have width := TransferScalarWideWalk01.symbolic_wide_walk_derives_final_width_and_modular_value 4 (words, 0) initialWidth
  have total := TransferScalarWideWalk01.symbolic_wide_walk_derives_final_value_below_twice_modulus 4 (words, 0) initialWidth initialBound
  have small := Nat.lt_trans total twice_actual_modulus_fits_four_word_radix
  have zero : (wideRounds 4 (words, 0)).2.toNat = 0 := by
    by_cases isZero : (wideRounds 4 (words, 0)).2.toNat = 0
    · exact isZero
    · have one : 1 ≤ (wideRounds 4 (words, 0)).2.toNat := by omega
      have lower := Nat.mul_le_mul_left (radix64 ^ 4) one
      rw [Nat.mul_one] at lower
      unfold wideValue at small
      omega
  have carryZero : (wideRounds 4 (words, 0)).2 = 0 := UInt64.toNat_inj.mp zero
  have lowBound : packWords (wideRounds 4 (words, 0)).1 < 2 * nullifierModulus := by
    simpa only [wideValue, zero, Nat.mul_zero, Nat.add_zero] using total
  exact ⟨width.1, carryZero, lowBound⟩

theorem single_subtraction_of_value_below_twice_modulus_is_canonical
    (value : Nat) (bound : value < 2 * nullifierModulus) :
    normalize nullifierModulus value < nullifierModulus := by
  by_cases enough : nullifierModulus ≤ value
  · rw [normalize, if_pos enough]; omega
  · rw [normalize, if_neg enough]; omega

theorem source_wide_reduction_derives_width_canonical_range_and_modular_relation
    (words : List UInt64) (eight : words.length = 8)
    (bound : packWords words < nullifierModulus * (radix64 ^ 4 + 1)) :
    (sourceWideReduce words).length = 4 ∧ packWords (sourceWideReduce words) < nullifierModulus ∧
      (radix64 ^ 4 * packWords (sourceWideReduce words)) % nullifierModulus = packWords words % nullifierModulus := by
  have raw := four_wide_rounds_derive_zero_discarded_carry_and_bounded_low_words words eight bound
  have reduced := TransferScalarMaskedNormalization01.source_sub_and_masked_addback_equal_single_modulus_normalization
    (wideRounds 4 (words, 0)).1 raw.1
  have relation := TransferScalarWideWalk01.symbolic_wide_walk_derives_final_width_and_modular_value
    4 (words, 0) (show (words, (0 : UInt64)).1.length = 4 + 4 from eight)
  have zero : (wideRounds 4 (words, 0)).2.toNat = 0 := by rw [raw.2.1]; rfl
  simp only [wideValue, zero, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at relation
  refine ⟨TransferScalarMaskedNormalization01.source_normalization_retains_four_word_width _ raw.1, ?_, ?_⟩
  · change packWords (sourceNormalize (wideRounds 4 (words, 0)).1) < nullifierModulus
    rw [reduced]
    exact single_subtraction_of_value_below_twice_modulus_is_canonical _ raw.2.2
  · change (radix64 ^ 4 * packWords (sourceNormalize (wideRounds 4 (words, 0)).1)) % nullifierModulus = _
    rw [reduced, Nat.mul_mod, TransferScalarMontgomeryValue01.single_modulus_normalization_preserves_modular_value,
      ← Nat.mul_mod]
    exact relation.2

theorem canonical_right_operand_source_multiplication_has_derived_montgomery_contract
    (self rhs : Vector UInt64 4) (canonical : packWords rhs.toList < nullifierModulus) :
    (sourceMulMontgomery self rhs).length = 4 ∧ packWords (sourceMulMontgomery self rhs) < nullifierModulus ∧
      (radix64 ^ 4 * packWords (sourceMulMontgomery self rhs)) % nullifierModulus =
        (packWords self.toList * packWords rhs.toList) % nullifierModulus := by
  have product := TransferScalarWideProduct01.source_schoolbook_product_has_exact_eight_limbs_value_and_range self rhs
  have range := canonical_right_operand_derives_full_product_range self rhs canonical
  have widened : packWords (sourceWideProduct self rhs) < nullifierModulus * (radix64 ^ 4 + 1) := by
    have step := Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self (radix64 ^ 4)) (by decide : 0 < nullifierModulus)
    exact Nat.lt_trans range step
  have contract := source_wide_reduction_derives_width_canonical_range_and_modular_relation
    (sourceWideProduct self rhs) product.1 widened
  rw [product.2.1] at contract
  exact contract

set_option pp.all true in
#check @sourceWideReduce
#print axioms sourceWideReduce
set_option pp.all true in
#check @sourceMulMontgomery
#print axioms sourceMulMontgomery
set_option pp.all true in
#check @twice_actual_modulus_fits_four_word_radix
#print axioms twice_actual_modulus_fits_four_word_radix
set_option pp.all true in
#check @canonical_right_operand_derives_full_product_range
#print axioms canonical_right_operand_derives_full_product_range
set_option pp.all true in
#check @four_wide_rounds_derive_zero_discarded_carry_and_bounded_low_words
#print axioms four_wide_rounds_derive_zero_discarded_carry_and_bounded_low_words
set_option pp.all true in
#check @single_subtraction_of_value_below_twice_modulus_is_canonical
#print axioms single_subtraction_of_value_below_twice_modulus_is_canonical
set_option pp.all true in
#check @source_wide_reduction_derives_width_canonical_range_and_modular_relation
#print axioms source_wide_reduction_derives_width_canonical_range_and_modular_relation
set_option pp.all true in
#check @canonical_right_operand_source_multiplication_has_derived_montgomery_contract
#print axioms canonical_right_operand_source_multiplication_has_derived_montgomery_contract
end ShielddSecurity.TransferScalarWideReduction01
