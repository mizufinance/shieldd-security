import ShielddSecurity.TransferScalarCanonicalSub01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarCanonicalNeg01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarBorrowWalk01 (borrowWalk)
open TransferScalarSbbPrimitive01 (borrowMask borrowBit)
open TransferScalarFourRoundWrapper01 (modulusWords)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Source neg uses four SBB steps for MODULUS-self and ignores final borrow
only because the private canonical invariant rules out underflow. It masks
every result limb with the wrapping-subtract Boolean OR-zero detector, so
zero returns zero rather than MODULUS. Symbolic recurrences derive all these
arithmetic outcomes. Native Rust/compiler/private Scalar binding is separate. -/

def orWalk (seed : UInt64) : List UInt64 → UInt64
  | [] => seed
  | word :: rest => orWalk (seed ||| word) rest

def sourceNegMask (words : List UInt64) : UInt64 :=
  (if orWalk 0 words = 0 then (1 : UInt64) else 0) - 1

def sourceNegWords (words : Vector UInt64 4) : List UInt64 :=
  let difference := borrowWalk false (modulusWords.zip words.toList)
  difference.1.map (fun word => word &&& sourceNegMask words.toList)

theorem symbolic_or_zero_detector_is_exact_packed_word_zero (seed : UInt64) (words : List UInt64) :
    orWalk seed words = 0 ↔ seed = 0 ∧ packWords words = 0 := by
  induction words generalizing seed with
  | nil => simp [orWalk, packWords]
  | cons word rest ih =>
    have packedCons : packWords (word :: rest) = 0 ↔ word = 0 ∧ packWords rest = 0 := by
      constructor
      · intro zero
        change word.toNat + radix64 * packWords rest = 0 at zero
        have head := Nat.eq_zero_of_add_eq_zero_left zero
        have product := Nat.eq_zero_of_add_eq_zero_right zero
        have tail : packWords rest = 0 := (Nat.mul_eq_zero.mp product).resolve_left (by decide)
        have wordZero : word = 0 := UInt64.toNat_inj.mp head
        exact ⟨wordZero, tail⟩
      · rintro ⟨wordZero, tail⟩
        rw [packWords, wordZero, tail, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
    rw [orWalk, ih, UInt64.or_eq_zero_iff, packedCons]
    exact and_assoc

theorem source_boolean_cast_wrapping_subtract_mask_selects_exact_zero_or_all_ones (words : List UInt64) :
    sourceNegMask words = if packWords words = 0 then 0 else 0xffff_ffff_ffff_ffff := by
  by_cases zero : packWords words = 0
  · have actual := (symbolic_or_zero_detector_is_exact_packed_word_zero 0 words).mpr ⟨rfl, zero⟩
    rw [sourceNegMask, if_pos actual, if_pos zero]
    rfl
  · have actual : ¬ orWalk 0 words = 0 := by
      intro impossible
      exact zero ((symbolic_or_zero_detector_is_exact_packed_word_zero 0 words).mp impossible).2
    rw [sourceNegMask, if_neg actual, if_neg zero]
    rfl

theorem source_four_sbb_and_nonzero_mask_derive_canonical_negation (scalar : CanonicalScalar) :
    (sourceNegWords scalar.words).length = 4 ∧
      packWords (sourceNegWords scalar.words) < nullifierModulus ∧
      packWords (sourceNegWords scalar.words) =
        (nullifierModulus - packWords scalar.words.toList) % nullifierModulus := by
  let difference := borrowWalk false (modulusWords.zip scalar.words.toList)
  have width : (modulusWords.zip scalar.words.toList).length = 4 := by
    rw [List.length_zip, TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs,
      Vector.length_toList, Nat.min_self]
  have firstProjection : modulusWords.length ≤ scalar.words.toList.length := by
    rw [TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs, Vector.length_toList]
    exact Nat.le_refl 4
  have secondProjection : scalar.words.toList.length ≤ modulusWords.length := by
    rw [TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs, Vector.length_toList]
    exact Nat.le_refl 4
  have differenceWidth : difference.1.length = 4 := by
    rw [TransferScalarBorrowWalk01.borrow_walk_retains_limb_count, width]
  have underflow := TransferScalarBorrowWalk01.final_borrow_is_exact_input_underflow
    (modulusWords.zip scalar.words.toList)
  rw [List.map_fst_zip firstProjection, List.map_snd_zip secondProjection,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus] at underflow
  change difference.2 = true ↔ nullifierModulus < packWords scalar.words.toList at underflow
  have noBorrow : difference.2 = false := by
    cases final : difference.2 with
    | false => rfl
    | true => exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt scalar.canonical)) (underflow.mp final))
  have conserved := TransferScalarBorrowWalk01.borrow_walk_conserves_full_subtraction_equation false
    (modulusWords.zip scalar.words.toList)
  rw [List.map_fst_zip firstProjection, List.map_snd_zip secondProjection,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus, width] at conserved
  change packWords difference.1 + packWords scalar.words.toList + borrowBit false =
    nullifierModulus + radix64 ^ 4 * borrowBit difference.2 at conserved
  rw [noBorrow] at conserved
  change packWords difference.1 + packWords scalar.words.toList = nullifierModulus at conserved
  have actualWidth : (sourceNegWords scalar.words).length = 4 := by
    change (difference.1.map (fun word => word &&& sourceNegMask scalar.words.toList)).length = 4
    rw [List.length_map, differenceWidth]
  refine ⟨actualWidth, ?_⟩
  change packWords (difference.1.map (fun word => word &&& sourceNegMask scalar.words.toList)) < nullifierModulus ∧
    packWords (difference.1.map (fun word => word &&& sourceNegMask scalar.words.toList)) =
      (nullifierModulus - packWords scalar.words.toList) % nullifierModulus
  rw [source_boolean_cast_wrapping_subtract_mask_selects_exact_zero_or_all_ones]
  by_cases zero : packWords scalar.words.toList = 0
  · rw [if_pos zero]
    change packWords (difference.1.map (fun word => word &&& borrowMask false)) < nullifierModulus ∧
      packWords (difference.1.map (fun word => word &&& borrowMask false)) = _
    rw [TransferScalarMaskedNormalization01.packing_masked_word_vector_selects_exact_value]
    change 0 < nullifierModulus ∧ 0 = (nullifierModulus - packWords scalar.words.toList) % nullifierModulus
    rw [zero, Nat.sub_zero, Nat.mod_self]
    exact ⟨by decide, rfl⟩
  · rw [if_neg zero]
    change packWords (difference.1.map (fun word => word &&& borrowMask true)) < nullifierModulus ∧
      packWords (difference.1.map (fun word => word &&& borrowMask true)) = _
    rw [TransferScalarMaskedNormalization01.packing_masked_word_vector_selects_exact_value]
    change packWords difference.1 < nullifierModulus ∧
      packWords difference.1 = (nullifierModulus - packWords scalar.words.toList) % nullifierModulus
    have positive : 0 < packWords scalar.words.toList := by omega
    have canonical : packWords difference.1 < nullifierModulus := by omega
    have value : packWords difference.1 = nullifierModulus - packWords scalar.words.toList := Nat.eq_sub_of_add_eq conserved
    refine ⟨canonical, ?_⟩
    rw [← value, Nat.mod_eq_of_lt canonical]

set_option pp.all true in
#check @orWalk
#print axioms orWalk
set_option pp.all true in
#check @sourceNegMask
#print axioms sourceNegMask
set_option pp.all true in
#check @sourceNegWords
#print axioms sourceNegWords
set_option pp.all true in
#check @symbolic_or_zero_detector_is_exact_packed_word_zero
#print axioms symbolic_or_zero_detector_is_exact_packed_word_zero
set_option pp.all true in
#check @source_boolean_cast_wrapping_subtract_mask_selects_exact_zero_or_all_ones
#print axioms source_boolean_cast_wrapping_subtract_mask_selects_exact_zero_or_all_ones
set_option pp.all true in
#check @source_four_sbb_and_nonzero_mask_derive_canonical_negation
#print axioms source_four_sbb_and_nonzero_mask_derive_canonical_negation
end ShielddSecurity.TransferScalarCanonicalNeg01
