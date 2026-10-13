import ShielddSecurity.TransferBlstArmFiveReduction01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmCiosStep01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferBlstArmMulRows01
open TransferBlstArmFiveReduction01
open TransferBlstArmCancellation01 (sourceArmMultiplier)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceMulAddRows sourceFiveFirstPass sourceFiveSecondPass

def sourceMulStepInput (operand accumulator : Vector UInt64 4) (digit : UInt64) : List UInt64 :=
  (sourceMulAddRows operand accumulator digit).1

theorem source_mul_step_input_is_exactly_its_head_and_four_word_tail
    (operand accumulator : Vector UInt64 4) (digit : UInt64) :
    sourceMulStepInput operand accumulator digit =
      (sourceMulStepInput operand accumulator digit).headD 0 :: (sourceMulStepInput operand accumulator digit).tail ∧
    (sourceMulStepInput operand accumulator digit).tail.length=4 := by
  have width : (sourceMulStepInput operand accumulator digit).length=5 :=
    source_mul_add_rows_retain_the_five_accumulator_words operand accumulator digit
  cases shape : sourceMulStepInput operand accumulator digit with
  | nil => rw [shape,List.length_nil] at width; omega
  | cons word rest =>
    rw [shape,List.length_cons] at width
    constructor
    · rfl
    · change rest.length=4
      omega

theorem canonical_operand_and_bounded_accumulator_derive_the_next_quotient_below_twice_modulus
    (operand : CanonicalScalar) (accumulator : Vector UInt64 4) (digit : UInt64)
    (prior : packWords accumulator.toList < 2*nullifierModulus) :
    (packWords (sourceMulStepInput operand.words accumulator digit)+
      (sourceArmMultiplier ((sourceMulStepInput operand.words accumulator digit).headD 0)).toNat*nullifierModulus)/radix64
      < 2*nullifierModulus := by
  have inputPacking := (canonical_operand_and_bounded_prior_accumulator_derive_no_discarded_product_overflow
    operand accumulator digit prior).2
  have digitBound : digit.toNat ≤ radix64-1 := by have := digit.toNat_lt; change digit.toNat < radix64 at this; omega
  have multiplierBound : (sourceArmMultiplier ((sourceMulStepInput operand.words accumulator digit).headD 0)).toNat ≤ radix64-1 := by
    have bounded : (sourceArmMultiplier ((sourceMulStepInput operand.words accumulator digit).headD 0)).toNat < radix64 :=
      (sourceArmMultiplier ((sourceMulStepInput operand.words accumulator digit).headD 0)).toNat_lt
    omega
  have digitProduct : digit.toNat*packWords operand.words.toList ≤ (radix64-1)*nullifierModulus :=
    Nat.mul_le_mul digitBound (Nat.le_of_lt operand.canonical)
  have modulusProduct : (sourceArmMultiplier ((sourceMulStepInput operand.words accumulator digit).headD 0)).toNat*nullifierModulus ≤
      (radix64-1)*nullifierModulus := Nat.mul_le_mul_right nullifierModulus multiplierBound
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < radix64)).mpr
  change packWords (sourceMulAddRows operand.words accumulator digit).1 + _ < _
  rw [inputPacking]
  have decomposition : 2*nullifierModulus + ((radix64-1)*nullifierModulus + (radix64-1)*nullifierModulus) =
      (2*nullifierModulus)*radix64 := by decide
  omega

def sourceMulStepWords (operand accumulator : Vector UInt64 4) (digit : UInt64) : List UInt64 :=
  let input := sourceMulStepInput operand accumulator digit
  (sourceFiveSecondPass (input.headD 0) input.tail).1

theorem bounded_original_multiplication_step_derives_both_zero_elimination_flags
    (operand : CanonicalScalar) (accumulator : Vector UInt64 4) (digit : UInt64)
    (prior : packWords accumulator.toList < 2*nullifierModulus) :
    (sourceFiveFirstPass ((sourceMulStepInput operand.words accumulator digit).headD 0)
      (sourceMulStepInput operand.words accumulator digit).tail).2=false ∧
    (sourceFiveSecondPass ((sourceMulStepInput operand.words accumulator digit).headD 0)
      (sourceMulStepInput operand.words accumulator digit).tail).2=false ∧
    packWords (sourceMulStepWords operand.words accumulator digit) =
      (packWords (sourceMulStepInput operand.words accumulator digit)+
        (sourceArmMultiplier ((sourceMulStepInput operand.words accumulator digit).headD 0)).toNat*nullifierModulus)/radix64 := by
  obtain ⟨shape,four⟩ := source_mul_step_input_is_exactly_its_head_and_four_word_tail operand.words accumulator digit
  have quotientBound := canonical_operand_and_bounded_accumulator_derive_the_next_quotient_below_twice_modulus operand accumulator digit prior
  have result := bounded_five_input_elimination_derives_both_zero_flags_and_the_exact_quotient
    ((sourceMulStepInput operand.words accumulator digit).headD 0)
    (sourceMulStepInput operand.words accumulator digit).tail four
    (by rw [← shape]; exact Nat.lt_trans quotientBound TransferScalarWideReduction01.twice_actual_modulus_fits_four_word_radix)
  rw [← shape] at result
  exact result

theorem original_multiplication_step_derives_width_range_and_exact_scaled_integer
    (operand : CanonicalScalar) (accumulator : Vector UInt64 4) (digit : UInt64)
    (prior : packWords accumulator.toList < 2*nullifierModulus) :
    (sourceMulStepWords operand.words accumulator digit).length=4 ∧
      packWords (sourceMulStepWords operand.words accumulator digit) < 2*nullifierModulus ∧
      radix64*packWords (sourceMulStepWords operand.words accumulator digit) =
        packWords accumulator.toList+digit.toNat*packWords operand.words.toList+
          (sourceArmMultiplier ((sourceMulStepInput operand.words accumulator digit).headD 0)).toNat*nullifierModulus := by
  obtain ⟨_,four⟩ := source_mul_step_input_is_exactly_its_head_and_four_word_tail operand.words accumulator digit
  have quotient := (bounded_original_multiplication_step_derives_both_zero_elimination_flags operand accumulator digit prior).2.2
  have width : (sourceMulStepWords operand.words accumulator digit).length=4 :=
    five_input_elimination_second_pass_retains_four_words _ _ four
  have below : packWords (sourceMulStepWords operand.words accumulator digit) < 2*nullifierModulus := by
    rw [quotient]
    exact canonical_operand_and_bounded_accumulator_derive_the_next_quotient_below_twice_modulus operand accumulator digit prior
  have divisible : (packWords (sourceMulStepInput operand.words accumulator digit)+
      (sourceArmMultiplier ((sourceMulStepInput operand.words accumulator digit).headD 0)).toNat*nullifierModulus)%radix64=0 := by
    rw [TransferBlstArmCancellation01.actual_arm_wrapped_multiplier_has_the_qualified_low_word_value]
    exact TransferScalarMontgomeryValue01.derived_round_numerator_is_divisible_by_radix _
  have fullInteger := Nat.mod_add_div (packWords (sourceMulStepInput operand.words accumulator digit)+
    (sourceArmMultiplier ((sourceMulStepInput operand.words accumulator digit).headD 0)).toNat*nullifierModulus) radix64
  rw [divisible,Nat.zero_add,← quotient] at fullInteger
  have inputPacking := (canonical_operand_and_bounded_prior_accumulator_derive_no_discarded_product_overflow
    operand accumulator digit prior).2
  change packWords (sourceMulStepInput operand.words accumulator digit) = _ at inputPacking
  rw [inputPacking] at fullInteger
  exact ⟨width,below,fullInteger⟩

/-- The intermediate state retains raw values below 2p; it does not assume
canonical normalization or a desired modular product. -/
def SourceIntermediate := { words : Vector UInt64 4 // packWords words.toList < 2*nullifierModulus }

def sourceCiosStep (operand : CanonicalScalar) (accumulator : SourceIntermediate) (digit : UInt64) : SourceIntermediate :=
  let output := sourceMulStepWords operand.words accumulator.val digit
  let contract := original_multiplication_step_derives_width_range_and_exact_scaled_integer operand accumulator.val digit accumulator.property
  ⟨⟨output.toArray,by rw [List.size_toArray]; exact contract.1⟩,by
    change packWords output.toArray.toList < 2*nullifierModulus
    rw [List.toList_toArray]
    exact contract.2.1⟩

theorem original_cios_step_fixed_vector_is_every_actual_output_word
    (operand : CanonicalScalar) (accumulator : SourceIntermediate) (digit : UInt64) :
    (sourceCiosStep operand accumulator digit).val.toList = sourceMulStepWords operand.words accumulator.val digit := by
  simp only [sourceCiosStep,Vector.toList,List.toList_toArray]

theorem original_cios_step_derives_the_full_scaled_integer_from_the_original_input
    (operand : CanonicalScalar) (accumulator : SourceIntermediate) (digit : UInt64) :
    radix64*packWords (sourceCiosStep operand accumulator digit).val.toList =
      packWords accumulator.val.toList + digit.toNat*packWords operand.words.toList+
        (sourceArmMultiplier ((sourceMulStepInput operand.words accumulator.val digit).headD 0)).toNat*nullifierModulus := by
  rw [original_cios_step_fixed_vector_is_every_actual_output_word]
  exact (original_multiplication_step_derives_width_range_and_exact_scaled_integer operand accumulator.val digit accumulator.property).2.2
set_option pp.all true in
#check @sourceMulStepInput
#print axioms sourceMulStepInput
set_option pp.all true in
#check @source_mul_step_input_is_exactly_its_head_and_four_word_tail
#print axioms source_mul_step_input_is_exactly_its_head_and_four_word_tail
set_option pp.all true in
#check @canonical_operand_and_bounded_accumulator_derive_the_next_quotient_below_twice_modulus
#print axioms canonical_operand_and_bounded_accumulator_derive_the_next_quotient_below_twice_modulus
set_option pp.all true in
#check @sourceMulStepWords
#print axioms sourceMulStepWords
set_option pp.all true in
#check @bounded_original_multiplication_step_derives_both_zero_elimination_flags
#print axioms bounded_original_multiplication_step_derives_both_zero_elimination_flags
set_option pp.all true in
#check @original_multiplication_step_derives_width_range_and_exact_scaled_integer
#print axioms original_multiplication_step_derives_width_range_and_exact_scaled_integer
set_option pp.all true in
#check @SourceIntermediate
#print axioms SourceIntermediate
set_option pp.all true in
#check @sourceCiosStep
#print axioms sourceCiosStep
set_option pp.all true in
#check @original_cios_step_fixed_vector_is_every_actual_output_word
#print axioms original_cios_step_fixed_vector_is_every_actual_output_word
set_option pp.all true in
#check @original_cios_step_derives_the_full_scaled_integer_from_the_original_input
#print axioms original_cios_step_derives_the_full_scaled_integer_from_the_original_input
end ShielddSecurity.TransferBlstArmCiosStep01
