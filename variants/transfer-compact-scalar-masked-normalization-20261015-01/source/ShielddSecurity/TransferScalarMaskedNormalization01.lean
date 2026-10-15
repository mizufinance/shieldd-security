import ShielddSecurity.TransferScalarBorrowWalk01
import Init.Data.UInt.Bitwise
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarMaskedNormalization01
open TransferScalarSerializationRange01 (radix64 normalize)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarCarrySchedule01 (macLoop)
open TransferScalarBorrowWalk01 (borrowWalk)
open TransferScalarSbbPrimitive01 (borrowMask borrowBit)
open TransferScalarFourRoundWrapper01 (modulusWords nativeRounds)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Source-shaped four-limb sub and borrow-masked ADC add-back. Final borrow
is derived from the exact SBB walk; each modulus limb uses actual UInt64 AND
with the source zero/all-ones mask. The retained low vector of the widened
unit MAC (ADC equivalent) implements normalization, with final carry discarded.
Source model range is derived from four finite raw words and the actual carry
wrapper; no desired underflow/result is supplied. Rust trace/endian remain interfaces. -/
def maskedModulus (borrow : Bool) : List UInt64 := modulusWords.map (fun word => word &&& borrowMask borrow)
def sourceNormalize (words : List UInt64) : List UInt64 :=
  let difference := borrowWalk false (words.zip modulusWords)
  (macLoop 1 0 (difference.1.zip (maskedModulus difference.2))).1

theorem word_and_reachable_borrow_mask_selects_exact_operand (word : UInt64) (borrow : Bool) :
    word &&& borrowMask borrow = if borrow then word else 0 := by
  cases borrow with
  | false => change word &&& 0 = 0; exact UInt64.and_zero
  | true => change word &&& (-1 : UInt64) = word; exact UInt64.and_neg_one

theorem packing_masked_word_vector_selects_exact_value (words : List UInt64) (borrow : Bool) :
    packWords (words.map (fun word => word &&& borrowMask borrow)) = if borrow then packWords words else 0 := by
  induction words generalizing borrow with
  | nil => cases borrow <;> rfl
  | cons word rest ih =>
    cases borrow with
    | false =>
      change (word &&& borrowMask false).toNat + radix64 * packWords (rest.map (fun word => word &&& borrowMask false)) = 0
      rw [word_and_reachable_borrow_mask_selects_exact_operand, ih false]
      rfl
    | true =>
      change (word &&& borrowMask true).toNat + radix64 * packWords (rest.map (fun word => word &&& borrowMask true)) = packWords (word :: rest)
      rw [word_and_reachable_borrow_mask_selects_exact_operand, ih true]
      rfl

theorem masked_modulus_retains_four_limb_width (borrow : Bool) : (maskedModulus borrow).length = 4 := by
  rw [maskedModulus, List.length_map, TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs]

theorem masked_modulus_packs_to_exact_selected_modulus (borrow : Bool) :
    packWords (maskedModulus borrow) = if borrow then nullifierModulus else 0 := by
  rw [maskedModulus, packing_masked_word_vector_selects_exact_value,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus]

theorem unit_mac_low_vector_is_full_sum_modulo_radix_power (pairs : List (UInt64 × UInt64)) :
    packWords (macLoop 1 0 pairs).1 =
      (packWords (pairs.map Prod.fst) + packWords (pairs.map Prod.snd)) % radix64 ^ pairs.length := by
  have conserved := TransferScalarCarrySchedule01.carry_walk_conserves_full_integer 1 0 pairs
  have bounded := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (macLoop 1 0 pairs).1
  rw [TransferScalarCarrySchedule01.carry_walk_retains_limb_count] at bounded
  simp only [UInt64.toNat_one, UInt64.toNat_zero, Nat.one_mul, Nat.add_zero] at conserved
  rw [← conserved, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bounded]

theorem source_normalization_retains_four_word_width (words : List UInt64) (four : words.length = 4) :
    (sourceNormalize words).length = 4 := by
  have zipped : (words.zip modulusWords).length = 4 := by
    rw [List.length_zip, four, TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs, Nat.min_self]
  have difference : (borrowWalk false (words.zip modulusWords)).1.length = 4 := by
    rw [TransferScalarBorrowWalk01.borrow_walk_retains_limb_count, zipped]
  unfold sourceNormalize
  rw [TransferScalarCarrySchedule01.carry_walk_retains_limb_count, List.length_zip, difference,
    masked_modulus_retains_four_limb_width, Nat.min_self]

theorem source_sub_and_masked_addback_equal_single_modulus_normalization
    (words : List UInt64) (four : words.length = 4) :
    packWords (sourceNormalize words) = normalize nullifierModulus (packWords words) := by
  let pairs := words.zip modulusWords
  let difference := borrowWalk false pairs
  have zipped : pairs.length = 4 := by
    rw [List.length_zip, four, TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs, Nat.min_self]
  have firstProjection : words.length ≤ modulusWords.length := by
    rw [four, TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs]
    exact Nat.le_refl 4
  have secondProjection : modulusWords.length ≤ words.length := by
    rw [four, TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs]
    exact Nat.le_refl 4
  have differenceFour : difference.1.length = 4 := by
    rw [TransferScalarBorrowWalk01.borrow_walk_retains_limb_count, zipped]
  have addWidth : (difference.1.zip (maskedModulus difference.2)).length = 4 := by
    rw [List.length_zip, differenceFour, masked_modulus_retains_four_limb_width, Nat.min_self]
  have addFirst : difference.1.length ≤ (maskedModulus difference.2).length := by
    rw [differenceFour, masked_modulus_retains_four_limb_width]
    exact Nat.le_refl 4
  have addSecond : (maskedModulus difference.2).length ≤ difference.1.length := by
    rw [differenceFour, masked_modulus_retains_four_limb_width]
    exact Nat.le_refl 4
  have conserved := TransferScalarBorrowWalk01.borrow_walk_conserves_full_subtraction_equation false pairs
  have underflow := TransferScalarBorrowWalk01.final_borrow_is_exact_input_underflow pairs
  have added := unit_mac_low_vector_is_full_sum_modulo_radix_power (difference.1.zip (maskedModulus difference.2))
  have differenceBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power difference.1
  have rawBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power words
  rw [differenceFour] at differenceBound
  rw [four] at rawBound
  rw [List.map_fst_zip firstProjection, List.map_snd_zip secondProjection,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus, zipped] at conserved
  rw [List.map_fst_zip firstProjection, List.map_snd_zip secondProjection,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus] at underflow
  rw [List.map_fst_zip addFirst, List.map_snd_zip addSecond, masked_modulus_packs_to_exact_selected_modulus, addWidth] at added
  change packWords (macLoop 1 0 (difference.1.zip (maskedModulus difference.2))).1 = normalize nullifierModulus (packWords words)
  change packWords difference.1 + nullifierModulus + borrowBit false =
    packWords words + radix64 ^ 4 * borrowBit difference.2 at conserved
  change difference.2 = true ↔ packWords words < nullifierModulus at underflow
  cases final : difference.2 with
  | false =>
    simp [borrowBit, final] at conserved added
    have enough : nullifierModulus ≤ packWords words := by omega
    have subtracted : packWords difference.1 = packWords words - nullifierModulus := Nat.eq_sub_of_add_eq conserved
    rw [normalize, if_pos enough, added, Nat.mod_eq_of_lt differenceBound, subtracted]
  | true =>
    simp [borrowBit, final] at conserved added
    have smaller : packWords words < nullifierModulus := underflow.mp final
    rw [normalize, if_neg (Nat.not_le_of_gt smaller), added, conserved, Nat.add_mod_right, Nat.mod_eq_of_lt rawBound]

theorem four_round_source_sub_and_addback_have_canonical_field_range
    (words : List UInt64) (four : words.length = 4) :
    packWords (sourceNormalize (nativeRounds 4 words)) < nullifierModulus := by
  rw [source_sub_and_masked_addback_equal_single_modulus_normalization _
    (TransferScalarFourRoundWrapper01.native_round_walk_preserves_four_word_width 4 words four)]
  exact TransferScalarFourRoundWrapper01.actual_four_round_carry_wrapper_normalizes_into_canonical_nullifier_field words four

set_option pp.all true in
#check @maskedModulus
#print axioms maskedModulus
set_option pp.all true in
#check @sourceNormalize
#print axioms sourceNormalize
set_option pp.all true in
#check @word_and_reachable_borrow_mask_selects_exact_operand
#print axioms word_and_reachable_borrow_mask_selects_exact_operand
set_option pp.all true in
#check @packing_masked_word_vector_selects_exact_value
#print axioms packing_masked_word_vector_selects_exact_value
set_option pp.all true in
#check @masked_modulus_retains_four_limb_width
#print axioms masked_modulus_retains_four_limb_width
set_option pp.all true in
#check @masked_modulus_packs_to_exact_selected_modulus
#print axioms masked_modulus_packs_to_exact_selected_modulus
set_option pp.all true in
#check @unit_mac_low_vector_is_full_sum_modulo_radix_power
#print axioms unit_mac_low_vector_is_full_sum_modulo_radix_power
set_option pp.all true in
#check @source_normalization_retains_four_word_width
#print axioms source_normalization_retains_four_word_width
set_option pp.all true in
#check @source_sub_and_masked_addback_equal_single_modulus_normalization
#print axioms source_sub_and_masked_addback_equal_single_modulus_normalization
set_option pp.all true in
#check @four_round_source_sub_and_addback_have_canonical_field_range
#print axioms four_round_source_sub_and_addback_have_canonical_field_range
end ShielddSecurity.TransferScalarMaskedNormalization01
