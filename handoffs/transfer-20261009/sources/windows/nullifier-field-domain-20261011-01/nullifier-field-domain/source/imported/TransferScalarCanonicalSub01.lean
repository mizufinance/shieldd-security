import ShielddSecurity.TransferScalarCanonicalAdd01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarCanonicalSub01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarBorrowWalk01 (borrowWalk)
open TransferScalarSbbPrimitive01 (borrowBit)
open TransferScalarMaskedNormalization01 (maskedModulus)
open TransferScalarCanonicalAdd01 (adcLoop)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Pinned Scalar.sub has four actual SBB steps then four ADC steps of the
borrow-masked modulus, discarding only the last carry. Canonical operands
derive canonical modular subtraction through the exact symbolic recurrences.
Source association is static; Rust/compiler/private Scalar binding is separate. -/

def sourceSubWords (left right : Vector UInt64 4) : List UInt64 :=
  let difference := borrowWalk false (left.toList.zip right.toList)
  (adcLoop 0 (difference.1.zip (maskedModulus difference.2))).1

theorem source_four_sbb_and_masked_adc_retain_four_output_limbs (left right : Vector UInt64 4) :
    (sourceSubWords left right).length = 4 := by
  have width : (left.toList.zip right.toList).length = 4 := by
    rw [List.length_zip, Vector.length_toList, Vector.length_toList, Nat.min_self]
  have differenceWidth : (borrowWalk false (left.toList.zip right.toList)).1.length = 4 := by
    rw [TransferScalarBorrowWalk01.borrow_walk_retains_limb_count, width]
  dsimp only [sourceSubWords]
  rw [TransferScalarCanonicalAdd01.symbolic_adc_walk_is_exact_unit_mac_walk,
    TransferScalarCarrySchedule01.carry_walk_retains_limb_count, List.length_zip, differenceWidth,
    TransferScalarMaskedNormalization01.masked_modulus_retains_four_limb_width, Nat.min_self]

theorem canonical_operands_source_subtraction_has_exact_canonical_modular_value (left right : CanonicalScalar) :
    packWords (sourceSubWords left.words right.words) < nullifierModulus ∧
      packWords (sourceSubWords left.words right.words) =
        (packWords left.words.toList + nullifierModulus - packWords right.words.toList) % nullifierModulus := by
  let difference := borrowWalk false (left.words.toList.zip right.words.toList)
  have width : (left.words.toList.zip right.words.toList).length = 4 := by
    rw [List.length_zip, Vector.length_toList, Vector.length_toList, Nat.min_self]
  have leftProjection : left.words.toList.length ≤ right.words.toList.length := by
    rw [Vector.length_toList, Vector.length_toList]; exact Nat.le_refl 4
  have rightProjection : right.words.toList.length ≤ left.words.toList.length := by
    rw [Vector.length_toList, Vector.length_toList]; exact Nat.le_refl 4
  have differenceWidth : difference.1.length = 4 := by
    rw [TransferScalarBorrowWalk01.borrow_walk_retains_limb_count, width]
  have addFirst : difference.1.length ≤ (maskedModulus difference.2).length := by
    rw [differenceWidth, TransferScalarMaskedNormalization01.masked_modulus_retains_four_limb_width]
    exact Nat.le_refl 4
  have addSecond : (maskedModulus difference.2).length ≤ difference.1.length := by
    rw [differenceWidth, TransferScalarMaskedNormalization01.masked_modulus_retains_four_limb_width]
    exact Nat.le_refl 4
  have addWidth : (difference.1.zip (maskedModulus difference.2)).length = 4 := by
    rw [List.length_zip, differenceWidth,
      TransferScalarMaskedNormalization01.masked_modulus_retains_four_limb_width, Nat.min_self]
  have conserved := TransferScalarBorrowWalk01.borrow_walk_conserves_full_subtraction_equation false
    (left.words.toList.zip right.words.toList)
  rw [List.map_fst_zip leftProjection, List.map_snd_zip rightProjection, width] at conserved
  change packWords difference.1 + packWords right.words.toList + borrowBit false =
    packWords left.words.toList + radix64 ^ 4 * borrowBit difference.2 at conserved
  have underflow := TransferScalarBorrowWalk01.final_borrow_is_exact_input_underflow
    (left.words.toList.zip right.words.toList)
  rw [List.map_fst_zip leftProjection, List.map_snd_zip rightProjection] at underflow
  change difference.2 = true ↔ packWords left.words.toList < packWords right.words.toList at underflow
  have added := TransferScalarMaskedNormalization01.unit_mac_low_vector_is_full_sum_modulo_radix_power
    (difference.1.zip (maskedModulus difference.2))
  rw [List.map_fst_zip addFirst, List.map_snd_zip addSecond,
    TransferScalarMaskedNormalization01.masked_modulus_packs_to_exact_selected_modulus, addWidth] at added
  have differenceBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power difference.1
  rw [differenceWidth] at differenceBound
  have leftBound := left.canonical
  have rightBound := right.canonical
  have radixBound := TransferScalarWideReduction01.twice_actual_modulus_fits_four_word_radix
  change packWords (adcLoop 0 (difference.1.zip (maskedModulus difference.2))).1 < nullifierModulus ∧
    packWords (adcLoop 0 (difference.1.zip (maskedModulus difference.2))).1 =
      (packWords left.words.toList + nullifierModulus - packWords right.words.toList) % nullifierModulus
  rw [TransferScalarCanonicalAdd01.symbolic_adc_walk_is_exact_unit_mac_walk, added]
  cases final : difference.2 with
  | false =>
    simp [borrowBit, final] at conserved
    rw [if_neg (by decide : ¬ (false : Bool) = true), Nat.add_zero, Nat.mod_eq_of_lt differenceBound]
    have canonical : packWords difference.1 < nullifierModulus := by omega
    have identity : packWords left.words.toList + nullifierModulus - packWords right.words.toList =
        packWords difference.1 + nullifierModulus := by omega
    refine ⟨canonical, ?_⟩
    rw [identity, Nat.add_mod_right, Nat.mod_eq_of_lt canonical]
  | true =>
    simp [borrowBit, final] at conserved
    rw [if_pos (rfl : (true : Bool) = true)]
    have smaller := underflow.mp final
    have canonical : packWords left.words.toList + nullifierModulus - packWords right.words.toList < nullifierModulus := by omega
    have sumIdentity : packWords difference.1 + nullifierModulus =
        (packWords left.words.toList + nullifierModulus - packWords right.words.toList) + radix64 ^ 4 := by omega
    have insideRadix : packWords left.words.toList + nullifierModulus - packWords right.words.toList < radix64 ^ 4 := by omega
    rw [sumIdentity, Nat.add_mod_right, Nat.mod_eq_of_lt insideRadix]
    exact ⟨canonical, (Nat.mod_eq_of_lt canonical).symm⟩

set_option pp.all true in
#check @sourceSubWords
#print axioms sourceSubWords
set_option pp.all true in
#check @source_four_sbb_and_masked_adc_retain_four_output_limbs
#print axioms source_four_sbb_and_masked_adc_retain_four_output_limbs
set_option pp.all true in
#check @canonical_operands_source_subtraction_has_exact_canonical_modular_value
#print axioms canonical_operands_source_subtraction_has_exact_canonical_modular_value
end ShielddSecurity.TransferScalarCanonicalSub01
