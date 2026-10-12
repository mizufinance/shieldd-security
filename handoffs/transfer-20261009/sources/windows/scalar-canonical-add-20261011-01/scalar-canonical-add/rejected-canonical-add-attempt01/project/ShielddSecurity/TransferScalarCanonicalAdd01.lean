import ShielddSecurity.TransferCheckedWordAcceptedInput01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarCanonicalAdd01
open TransferScalarSerializationRange01 (radix64 normalize)
open TransferScalarWordPrimitives01 (packWords mac128 split128)
open TransferScalarAdcShift01 (adc64)
open TransferScalarCarrySchedule01 (macLoop)
open TransferScalarMaskedNormalization01 (sourceNormalize)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! The pinned Scalar.add performs four ADC steps, discards the last carry,
then invokes Scalar.sub(MODULUS). Its source-shaped SBB/masked-ADC model
is sourceNormalize. Canonical operands derive zero discarded carry and a
canonical modular sum. This is one operation's arithmetic model; private
Scalar construction, Rust primitives/compiler and native caller binding
remain independent. No native testing or certification credit. -/

def adcLoop (carry : UInt64) : List (UInt64 × UInt64) → List UInt64 × UInt64
  | [] => ([], carry)
  | pair :: rest =>
    let step := adc64 pair.1 pair.2 carry
    let after := adcLoop step.2 rest
    (step.1 :: after.1, after.2)

def sourceAddWords (left right : Vector UInt64 4) : List UInt64 :=
  sourceNormalize (adcLoop 0 (left.toList.zip right.toList)).1

theorem symbolic_adc_walk_is_exact_unit_mac_walk (carry : UInt64) (pairs : List (UInt64 × UInt64)) :
    adcLoop carry pairs = macLoop 1 carry pairs := by
  induction pairs generalizing carry with
  | nil => rfl
  | cons pair rest ih =>
    have step : adc64 pair.1 pair.2 carry = split128 (mac128 pair.1 1 pair.2 carry) := by
      rw [adc64, TransferScalarAdcShift01.fixed_high_shift_and_cast_equals_radix_quotient_pair,
        TransferScalarAdcShift01.widened_adc_is_unit_multiplier_mac]
    simp only [adcLoop, macLoop, step, ih]

theorem canonical_operands_derive_four_adc_limbs_zero_carry_and_exact_sum (left right : CanonicalScalar) :
    (adcLoop 0 (left.words.toList.zip right.words.toList)).1.length = 4 ∧
      (adcLoop 0 (left.words.toList.zip right.words.toList)).2.toNat = 0 ∧
      packWords (adcLoop 0 (left.words.toList.zip right.words.toList)).1 =
        packWords left.words.toList + packWords right.words.toList := by
  have width : (left.words.toList.zip right.words.toList).length = 4 := by
    rw [List.length_zip, Vector.length_toList, Vector.length_toList, Nat.min_self]
  have leftProjection : left.words.toList.length ≤ right.words.toList.length := by
    rw [Vector.length_toList, Vector.length_toList]
  have rightProjection : right.words.toList.length ≤ left.words.toList.length := by
    rw [Vector.length_toList, Vector.length_toList]
  have conserved := TransferScalarCarrySchedule01.carry_walk_conserves_full_integer 1 0
    (left.words.toList.zip right.words.toList)
  rw [List.map_fst_zip leftProjection, List.map_snd_zip rightProjection, width,
    UInt64.toNat_one, UInt64.toNat_zero, Nat.one_mul, Nat.add_zero] at conserved
  have sumBound : packWords left.words.toList + packWords right.words.toList < 2 * nullifierModulus := by
    have l := left.canonical
    have r := right.canonical
    omega
  have radixBound := TransferScalarWideReduction01.twice_actual_modulus_fits_four_word_radix
  have sumRadix := Nat.lt_trans sumBound radixBound
  have zeroCarry : (macLoop 1 0 (left.words.toList.zip right.words.toList)).2.toNat = 0 := by
    by_cases zero : (macLoop 1 0 (left.words.toList.zip right.words.toList)).2.toNat = 0
    · exact zero
    · have positive : 1 ≤ (macLoop 1 0 (left.words.toList.zip right.words.toList)).2.toNat := by omega
      have product := Nat.mul_le_mul_left (radix64 ^ 4) positive
      rw [Nat.mul_one] at product
      omega
  rw [symbolic_adc_walk_is_exact_unit_mac_walk]
  refine ⟨?_, zeroCarry, ?_⟩
  · rw [TransferScalarCarrySchedule01.carry_walk_retains_limb_count, width]
  · rw [zeroCarry, Nat.mul_zero, Nat.add_zero] at conserved
    exact conserved

theorem source_four_adc_and_modulus_sub_preserve_canonical_modular_sum (left right : CanonicalScalar) :
    (sourceAddWords left.words right.words).length = 4 ∧
      packWords (sourceAddWords left.words right.words) < nullifierModulus ∧
      packWords (sourceAddWords left.words right.words) =
        (packWords left.words.toList + packWords right.words.toList) % nullifierModulus := by
  obtain ⟨width, _, value⟩ := canonical_operands_derive_four_adc_limbs_zero_carry_and_exact_sum left right
  have sumBound : packWords left.words.toList + packWords right.words.toList < 2 * nullifierModulus := by
    have l := left.canonical
    have r := right.canonical
    omega
  have normalized := TransferScalarMaskedNormalization01.source_sub_and_masked_addback_equal_single_modulus_normalization
    (adcLoop 0 (left.words.toList.zip right.words.toList)).1 width
  rw [value] at normalized
  refine ⟨TransferScalarMaskedNormalization01.source_normalization_retains_four_word_width _ width, ?_, ?_⟩
  · change packWords (sourceNormalize _) < nullifierModulus
    rw [normalized]
    exact TransferScalarWideReduction01.single_subtraction_of_value_below_twice_modulus_is_canonical _ sumBound
  · change packWords (sourceNormalize _) = _
    rw [normalized]
    by_cases enough : nullifierModulus ≤ packWords left.words.toList + packWords right.words.toList
    · rw [normalize, if_pos enough]
      have differenceBound : packWords left.words.toList + packWords right.words.toList - nullifierModulus < nullifierModulus := by omega
      have decomposition : packWords left.words.toList + packWords right.words.toList =
          (packWords left.words.toList + packWords right.words.toList - nullifierModulus) + nullifierModulus := by omega
      rw [decomposition, Nat.add_mod_right, Nat.mod_eq_of_lt differenceBound]
    · rw [normalize, if_neg enough, Nat.mod_eq_of_lt (Nat.lt_of_not_ge enough)]

set_option pp.all true in
#check @adcLoop
#print axioms adcLoop
set_option pp.all true in
#check @sourceAddWords
#print axioms sourceAddWords
set_option pp.all true in
#check @symbolic_adc_walk_is_exact_unit_mac_walk
#print axioms symbolic_adc_walk_is_exact_unit_mac_walk
set_option pp.all true in
#check @canonical_operands_derive_four_adc_limbs_zero_carry_and_exact_sum
#print axioms canonical_operands_derive_four_adc_limbs_zero_carry_and_exact_sum
set_option pp.all true in
#check @source_four_adc_and_modulus_sub_preserve_canonical_modular_sum
#print axioms source_four_adc_and_modulus_sub_preserve_canonical_modular_sum
end ShielddSecurity.TransferScalarCanonicalAdd01
