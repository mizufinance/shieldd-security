import ShielddSecurity.TransferBlstArmSqrtSearch01
import ShielddSecurity.TransferBlstArmAdd01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmRedc01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64 normalize)
open TransferScalarFourRoundWrapper01 (nativeRounds roundMultipliers)
open TransferBlstArmReduction01 (sourceArmReductionRounds)
open TransferBlstArmAdd01 (sourceArmAddRaw sourceArmAddWords)
open TransferBlstArmNormalized01 (sourceArmBorrowSelect)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceArmReductionRounds sourceArmAddWords sourceArmBorrowSelect

/-! Locked ARM redc_mont_256 reduces the low four words before adding the
high four words and executing the fifth SBCS/CSEL. All raw high-half words are accepted; the fifth carry and borrow are retained. No inverse result or native execution is
assumed or inferred. -/

def sourceRedcLow (low : Vector UInt64 4) : Vector UInt64 4 :=
  ⟨(sourceArmReductionRounds 4 low.toList).toArray,by
    rw [List.size_toArray,
      TransferBlstArmReduction01.symbolic_actual_arm_reduction_rounds_equal_the_qualified_word_recurrence 4 low.toList Vector.length_toList]
    exact TransferScalarFourRoundWrapper01.native_round_walk_preserves_four_word_width 4 low.toList Vector.length_toList⟩

theorem original_redc_low_vector_retains_the_exact_four_round_output (low : Vector UInt64 4) :
    (sourceRedcLow low).toList = nativeRounds 4 low.toList := by
  simp only [sourceRedcLow,Vector.toList,List.toList_toArray]
  exact TransferBlstArmReduction01.symbolic_actual_arm_reduction_rounds_equal_the_qualified_word_recurrence 4 low.toList Vector.length_toList

theorem original_redc_low_half_derives_at_most_the_modulus (low : Vector UInt64 4) :
    packWords (sourceRedcLow low).toList ≤ nullifierModulus := by
  rw [original_redc_low_vector_retains_the_exact_four_round_output,
    TransferScalarFourRoundWrapper01.native_carry_rounds_pack_to_symbolic_reduction 4 low.toList Vector.length_toList]
  have bounded := TransferScalarSerializationRange01.all_rounds_finish_at_most_modulus
    nullifierModulus radix64 (roundMultipliers 4 low.toList) (by decide)
    (TransferScalarFourRoundWrapper01.every_derived_multiplier_is_a_finite_u64_word 4 low.toList)
    (packWords low.toList) (by
      rw [TransferScalarFourRoundWrapper01.derived_multiplier_vector_has_round_count]
      have raw := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power low.toList
      rw [Vector.length_toList] at raw
      exact Nat.lt_of_lt_of_le raw (Nat.le_add_left _ _))
  omega

theorem original_redc_low_half_derives_the_four_round_weighted_relation (low : Vector UInt64 4) :
    (radix64^4 * packWords (sourceRedcLow low).toList)%nullifierModulus = packWords low.toList%nullifierModulus := by
  rw [original_redc_low_vector_retains_the_exact_four_round_output]
  exact TransferScalarMontgomeryValue01.symbolic_native_round_walk_preserves_montgomery_modular_value 4 low.toList Vector.length_toList


theorem original_fifth_borrow_flag_is_exact_overflow_and_low_borrow
    (carry borrow : Bool) :
    TransferScalarBorrowWalk01.nextBorrow (UInt64.ofNat carry.toNat) 0 borrow = (!carry && borrow) := by
  cases carry <;> cases borrow <;> decide

theorem original_four_word_add_and_fifth_borrow_select_derive_exact_normalization
    (left right : Vector UInt64 4)
    (bounded : packWords left.toList + packWords right.toList < radix64^4 + nullifierModulus) :
    packWords (sourceArmAddWords left right) = normalize nullifierModulus
      (packWords left.toList + packWords right.toList) := by
  have leftProjection : left.toList.length ≤ right.toList.length := by rw [Vector.length_toList,Vector.length_toList]
  have rightProjection : right.toList.length ≤ left.toList.length := by rw [Vector.length_toList,Vector.length_toList]
  have sumEquation := TransferBlstArmCarryChains01.symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    false (left.toList.zip right.toList)
  rw [List.map_fst_zip leftProjection,List.map_snd_zip rightProjection,List.length_zip,
    Vector.length_toList,Vector.length_toList,Nat.min_self] at sumEquation
  change packWords (sourceArmAddRaw left right).1 + radix64^4*(sourceArmAddRaw left right).2.toNat =
    packWords left.toList + packWords right.toList + 0 at sumEquation
  have width := TransferBlstArmAdd01.source_arm_add_raw_retains_four_limbs left right
  have modWidth := TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs
  have sumProjection : (sourceArmAddRaw left right).1.length ≤ TransferScalarFourRoundWrapper01.modulusWords.length := by rw [width,modWidth]
  have modProjection : TransferScalarFourRoundWrapper01.modulusWords.length ≤ (sourceArmAddRaw left right).1.length := by rw [width,modWidth]
  have differenceEquation := TransferScalarBorrowWalk01.borrow_walk_conserves_full_subtraction_equation
    false ((sourceArmAddRaw left right).1.zip TransferScalarFourRoundWrapper01.modulusWords)
  rw [List.map_fst_zip sumProjection,List.map_snd_zip modProjection,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus,
    List.length_zip,width,modWidth,Nat.min_self] at differenceEquation
  simp only [TransferScalarSbbPrimitive01.borrowBit,Bool.false_eq_true,if_false,Nat.add_zero] at differenceEquation
  have underflow := TransferScalarBorrowWalk01.final_borrow_is_exact_input_underflow
    ((sourceArmAddRaw left right).1.zip TransferScalarFourRoundWrapper01.modulusWords)
  rw [List.map_fst_zip sumProjection,List.map_snd_zip modProjection,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus] at underflow
  have radixBound := TransferScalarWideReduction01.twice_actual_modulus_fits_four_word_radix
  rw [sourceArmAddWords,original_fifth_borrow_flag_is_exact_overflow_and_low_borrow]
  cases carryEq : (sourceArmAddRaw left right).2 <;>
    cases borrowEq : (TransferScalarBorrowWalk01.borrowWalk false
      ((sourceArmAddRaw left right).1.zip TransferScalarFourRoundWrapper01.modulusWords)).2
  all_goals simp only [carryEq,borrowEq,Bool.toNat_false,Bool.toNat_true,
    Bool.not_false,Bool.not_true,Bool.true_and,Bool.false_and,Bool.false_eq_true,if_false,if_true,
    Nat.mul_zero,Nat.mul_one,Nat.add_zero] at sumEquation differenceEquation ⊢
  · have enough : nullifierModulus ≤ packWords left.toList + packWords right.toList := by omega
    rw [TransferScalarSerializationRange01.normalize,if_pos enough]
    omega
  · have rawBelow := underflow.mp borrowEq
    have below : packWords left.toList + packWords right.toList < nullifierModulus := by omega
    rw [TransferScalarSerializationRange01.normalize,if_neg (Nat.not_le_of_lt below)]
    omega
  · omega
  · have enough : nullifierModulus ≤ packWords left.toList + packWords right.toList := by omega
    rw [TransferScalarSerializationRange01.normalize,if_pos enough]
    omega

def sourceRedcWords (low high : Vector UInt64 4) : List UInt64 :=
  sourceArmAddWords (sourceRedcLow low) high

theorem original_redc_all_raw_high_words_derive_exact_normalized_sum (low high : Vector UInt64 4) :
    packWords (sourceRedcWords low high) = normalize nullifierModulus
      (packWords (sourceRedcLow low).toList + packWords high.toList) := by
  apply original_four_word_add_and_fifth_borrow_select_derive_exact_normalization
  have lowBound := original_redc_low_half_derives_at_most_the_modulus low
  have highBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power high.toList
  rw [Vector.length_toList] at highBound
  omega

theorem original_redc_all_raw_high_words_retain_four_output_words (low high : Vector UInt64 4) :
    (sourceRedcWords low high).length = 4 := by
  have width := TransferBlstArmAdd01.source_arm_add_raw_retains_four_limbs (sourceRedcLow low) high
  have differenceWidth :
      (TransferScalarBorrowWalk01.borrowWalk false ((sourceArmAddRaw (sourceRedcLow low) high).1.zip
        TransferScalarFourRoundWrapper01.modulusWords)).1.length = 4 := by
    rw [TransferScalarBorrowWalk01.borrow_walk_retains_limb_count,List.length_zip,width,
      TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs,Nat.min_self]
  rw [sourceRedcWords,sourceArmAddWords]
  split
  · exact width
  · exact differenceWidth

theorem original_redc_derives_the_entire_wide_input_weighted_modular_relation
    (low high : Vector UInt64 4) :
    (radix64^4 * packWords (sourceRedcWords low high))%nullifierModulus =
      (packWords low.toList + radix64^4 * packWords high.toList)%nullifierModulus := by
  have normalized : packWords (sourceRedcWords low high)%nullifierModulus =
      (packWords (sourceRedcLow low).toList + packWords high.toList)%nullifierModulus := by
    rw [original_redc_all_raw_high_words_derive_exact_normalized_sum]
    exact TransferScalarMontgomeryValue01.single_modulus_normalization_preserves_modular_value _
  calc
    _ = (radix64^4 * (packWords (sourceRedcLow low).toList + packWords high.toList))%nullifierModulus := by
      rw [Nat.mul_mod,normalized,← Nat.mul_mod]
    _ = (radix64^4 * packWords (sourceRedcLow low).toList + radix64^4 * packWords high.toList)%nullifierModulus := by
      rw [Nat.mul_add]
    _ = _ := by
      rw [Nat.add_mod,original_redc_low_half_derives_the_four_round_weighted_relation,← Nat.add_mod]

set_option pp.all true in
#check @sourceRedcLow
#print axioms sourceRedcLow
set_option pp.all true in
#check @original_redc_low_vector_retains_the_exact_four_round_output
#print axioms original_redc_low_vector_retains_the_exact_four_round_output
set_option pp.all true in
#check @original_redc_low_half_derives_at_most_the_modulus
#print axioms original_redc_low_half_derives_at_most_the_modulus
set_option pp.all true in
#check @original_redc_low_half_derives_the_four_round_weighted_relation
#print axioms original_redc_low_half_derives_the_four_round_weighted_relation
set_option pp.all true in
#check @original_fifth_borrow_flag_is_exact_overflow_and_low_borrow
#print axioms original_fifth_borrow_flag_is_exact_overflow_and_low_borrow
set_option pp.all true in
#check @original_four_word_add_and_fifth_borrow_select_derive_exact_normalization
#print axioms original_four_word_add_and_fifth_borrow_select_derive_exact_normalization
set_option pp.all true in
#check @sourceRedcWords
#print axioms sourceRedcWords
set_option pp.all true in
#check @original_redc_all_raw_high_words_derive_exact_normalized_sum
#print axioms original_redc_all_raw_high_words_derive_exact_normalized_sum
set_option pp.all true in
#check @original_redc_all_raw_high_words_retain_four_output_words
#print axioms original_redc_all_raw_high_words_retain_four_output_words
set_option pp.all true in
#check @original_redc_derives_the_entire_wide_input_weighted_modular_relation
#print axioms original_redc_derives_the_entire_wide_input_weighted_modular_relation
end ShielddSecurity.TransferBlstArmRedc01
