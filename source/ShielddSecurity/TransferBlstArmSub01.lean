import ShielddSecurity.TransferBlstArmCneg01
import ShielddSecurity.TransferBlstArmCarryChains01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmSub01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferScalarBorrowWalk01 (borrowWalk)
open TransferScalarMaskedNormalization01 (maskedModulus)
open TransferBlstArmCarryChains01 (sourceAddCarryChain)
open TransferScalarCanonicalAdd01 (adcLoop)
open TransferBlstArmNormalized01 (sourceBlstFrWordMeaning)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceAddCarryChain adcLoop borrowWalk
  TransferScalarCarrySchedule01.macLoop

theorem actual_arm_add_chain_zero_seed_low_integer_is_exact_full_sum_modulo_radix
    (pairs : List (UInt64 × UInt64)) :
    packWords (sourceAddCarryChain false pairs).1 =
      (packWords (pairs.map Prod.fst) + packWords (pairs.map Prod.snd)) % radix64^pairs.length := by
  have conserved := TransferBlstArmCarryChains01.symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag false pairs
  have bounded := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (sourceAddCarryChain false pairs).1
  rw [TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count] at bounded
  change packWords (sourceAddCarryChain false pairs).1 +
    radix64^pairs.length*(sourceAddCarryChain false pairs).2.toNat =
      packWords (pairs.map Prod.fst) + packWords (pairs.map Prod.snd) + 0 at conserved
  simp only [Nat.add_zero] at conserved
  rw [← conserved,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bounded]

theorem actual_arm_add_chain_zero_seed_derives_every_qualified_adc_low_word
    (pairs : List (UInt64 × UInt64)) :
    (sourceAddCarryChain false pairs).1 = (adcLoop 0 pairs).1 := by
  apply TransferCanonicalWordEquality01.equal_width_packed_u64_lists_are_equal
  · rw [TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
      TransferScalarCanonicalAdd01.symbolic_adc_walk_is_exact_unit_mac_walk,
      TransferScalarCarrySchedule01.carry_walk_retains_limb_count]
  · rw [actual_arm_add_chain_zero_seed_low_integer_is_exact_full_sum_modulo_radix,
      TransferScalarCanonicalAdd01.symbolic_adc_walk_is_exact_unit_mac_walk,
      TransferScalarMaskedNormalization01.unit_mac_low_vector_is_full_sum_modulo_radix_power]

/-- Locked sub_mod_256 arithmetic: SUBS/SBCS low subtraction, SBC zero/all-ones
mask, AND of modulus limbs and ADDS/ADCS/ADC add-back. Final carry is discarded
as in the source. Native ISA, pointer/ABI and compiler execution remain open. -/
def sourceArmSubWords (left right : Vector UInt64 4) : List UInt64 :=
  let difference := borrowWalk false (left.toList.zip right.toList)
  (sourceAddCarryChain false (difference.1.zip (maskedModulus difference.2))).1

theorem actual_arm_sub_derives_every_qualified_sdk_output_word (left right : Vector UInt64 4) :
    sourceArmSubWords left right = TransferScalarCanonicalSub01.sourceSubWords left right := by
  rw [sourceArmSubWords,actual_arm_add_chain_zero_seed_derives_every_qualified_adc_low_word]
  rfl

theorem actual_arm_sub_derives_the_four_limb_output_width (left right : Vector UInt64 4) :
    (sourceArmSubWords left right).length = 4 := by
  rw [actual_arm_sub_derives_every_qualified_sdk_output_word]
  exact TransferScalarCanonicalSub01.source_four_sbb_and_masked_adc_retain_four_output_limbs left right

theorem canonical_actual_arm_sub_derives_the_canonical_raw_difference (left right : CanonicalScalar) :
    packWords (sourceArmSubWords left.words right.words) < nullifierModulus ∧
      packWords (sourceArmSubWords left.words right.words) =
        (packWords left.words.toList + nullifierModulus - packWords right.words.toList) % nullifierModulus := by
  rw [actual_arm_sub_derives_every_qualified_sdk_output_word]
  exact TransferScalarCanonicalSub01.canonical_operands_source_subtraction_has_exact_canonical_modular_value left right

def sourceArmSub (left right : CanonicalScalar) : CanonicalScalar :=
  TransferScalarProgramInvariant01.certifyResult (sourceArmSubWords left.words right.words)
    (actual_arm_sub_derives_the_four_limb_output_width _ _)
    (canonical_actual_arm_sub_derives_the_canonical_raw_difference left right).1

theorem canonical_actual_arm_sub_derives_the_original_input_field_difference (left right : CanonicalScalar) :
    sourceBlstFrWordMeaning (sourceArmSub left right).words =
      sourceBlstFrWordMeaning left.words - sourceBlstFrWordMeaning right.words := by
  have output : packWords (sourceArmSub left right).words.toList =
      (packWords left.words.toList + nullifierModulus - packWords right.words.toList) % nullifierModulus := by
    change packWords (sourceArmSubWords left.words right.words).toArray.toList = _
    rw [List.toList_toArray]
    exact (canonical_actual_arm_sub_derives_the_canonical_raw_difference left right).2
  have subtractionDefined : packWords right.words.toList ≤ packWords left.words.toList + nullifierModulus := by
    have bounded := right.canonical
    omega
  rw [TransferBlstArmCneg01.original_fr_word_meaning_is_the_raw_montgomery_residue,output,
    ZMod.natCast_mod,Nat.cast_sub subtractionDefined,Nat.cast_add,ZMod.natCast_self,add_zero,mul_sub,
    ← TransferBlstArmCneg01.original_fr_word_meaning_is_the_raw_montgomery_residue,
    ← TransferBlstArmCneg01.original_fr_word_meaning_is_the_raw_montgomery_residue]
set_option pp.all true in
#check @actual_arm_add_chain_zero_seed_low_integer_is_exact_full_sum_modulo_radix
#print axioms actual_arm_add_chain_zero_seed_low_integer_is_exact_full_sum_modulo_radix
set_option pp.all true in
#check @actual_arm_add_chain_zero_seed_derives_every_qualified_adc_low_word
#print axioms actual_arm_add_chain_zero_seed_derives_every_qualified_adc_low_word
set_option pp.all true in
#check @sourceArmSubWords
#print axioms sourceArmSubWords
set_option pp.all true in
#check @actual_arm_sub_derives_every_qualified_sdk_output_word
#print axioms actual_arm_sub_derives_every_qualified_sdk_output_word
set_option pp.all true in
#check @actual_arm_sub_derives_the_four_limb_output_width
#print axioms actual_arm_sub_derives_the_four_limb_output_width
set_option pp.all true in
#check @canonical_actual_arm_sub_derives_the_canonical_raw_difference
#print axioms canonical_actual_arm_sub_derives_the_canonical_raw_difference
set_option pp.all true in
#check @sourceArmSub
#print axioms sourceArmSub
set_option pp.all true in
#check @canonical_actual_arm_sub_derives_the_original_input_field_difference
#print axioms canonical_actual_arm_sub_derives_the_original_input_field_difference
end ShielddSecurity.TransferBlstArmSub01
