import ShielddSecurity.TransferBlstArmCneg01
import ShielddSecurity.TransferBlstArmProducts01
import ShielddSecurity.TransferBlstArmCarryChains01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmMulRows01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferBlstArmProducts01 (sourceProductLowWords sourceProductHighWords)
open TransferBlstArmCarryChains01 (sourceAddCarryChain)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceAddCarryChain sourceProductLowWords sourceProductHighWords

/-- Arithmetic low-product additions in mul_mont_sparse_256. The zero
accumulator specializes the initial product block; subsequent blocks add the
four prior accumulator words. Native instruction/ABI execution is separate. -/
def sourceMulAddLowPhase (operand accumulator : Vector UInt64 4) (digit : UInt64) : List UInt64 × Bool :=
  sourceAddCarryChain false (accumulator.toList.zip (sourceProductLowWords digit operand.toList))

theorem source_mul_add_low_phase_retains_the_four_low_words
    (operand accumulator : Vector UInt64 4) (digit : UInt64) :
    (sourceMulAddLowPhase operand accumulator digit).1.length = 4 := by
  rw [sourceMulAddLowPhase,TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
    List.length_zip,(TransferBlstArmProducts01.source_product_vectors_retain_the_source_modulus_limb_count digit operand.toList).1,
    Vector.length_toList,Vector.length_toList,Nat.min_self]

theorem boolean_carry_word_retains_the_exact_flag_integer (flag : Bool) :
    (UInt64.ofNat flag.toNat).toNat = flag.toNat := by
  cases flag <;> rfl

def sourceMulAddLowFive (operand accumulator : Vector UInt64 4) (digit : UInt64) : List UInt64 :=
  let first := sourceMulAddLowPhase operand accumulator digit
  first.1 ++ [UInt64.ofNat first.2.toNat]

theorem source_mul_add_extended_low_phase_retains_five_words
    (operand accumulator : Vector UInt64 4) (digit : UInt64) :
    (sourceMulAddLowFive operand accumulator digit).length = 5 := by
  rw [sourceMulAddLowFive,List.length_append,source_mul_add_low_phase_retains_the_four_low_words]
  rfl

theorem source_mul_add_extended_low_phase_derives_the_full_low_product_sum
    (operand accumulator : Vector UInt64 4) (digit : UInt64) :
    packWords (sourceMulAddLowFive operand accumulator digit) =
      packWords accumulator.toList + packWords (sourceProductLowWords digit operand.toList) := by
  have productWidth : (sourceProductLowWords digit operand.toList).length = 4 :=
    (TransferBlstArmProducts01.source_product_vectors_retain_the_source_modulus_limb_count digit operand.toList).1.trans Vector.length_toList
  have leftProjection : accumulator.toList.length ≤ (sourceProductLowWords digit operand.toList).length := by
    rw [Vector.length_toList,productWidth]
  have rightProjection : (sourceProductLowWords digit operand.toList).length ≤ accumulator.toList.length := by
    rw [productWidth,Vector.length_toList]
  have first := TransferBlstArmCarryChains01.symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    false (accumulator.toList.zip (sourceProductLowWords digit operand.toList))
  rw [List.map_fst_zip leftProjection,List.map_snd_zip rightProjection,
    List.length_zip,Vector.length_toList,productWidth,Nat.min_self] at first
  rw [sourceMulAddLowFive,TransferScalarCarrySchedule01.packing_append_preserves_positional_value,
    source_mul_add_low_phase_retains_the_four_low_words]
  simpa only [sourceMulAddLowPhase,packWords,boolean_carry_word_retains_the_exact_flag_integer,
    Nat.mul_zero,Nat.add_zero] using first

/-- Shifted high products are added after the four low products, retaining
the fifth word before the Montgomery elimination block. The final flag is a
mathematical overflow witness; native ADC instruction correspondence is open. -/
def sourceMulAddRows (operand accumulator : Vector UInt64 4) (digit : UInt64) : List UInt64 × Bool :=
  sourceAddCarryChain false ((sourceMulAddLowFive operand accumulator digit).zip
    (0 :: sourceProductHighWords digit operand.toList))

theorem source_mul_add_rows_retain_the_five_accumulator_words
    (operand accumulator : Vector UInt64 4) (digit : UInt64) :
    (sourceMulAddRows operand accumulator digit).1.length = 5 := by
  rw [sourceMulAddRows,TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
    List.length_zip,source_mul_add_extended_low_phase_retains_five_words,List.length_cons,
    (TransferBlstArmProducts01.source_product_vectors_retain_the_source_modulus_limb_count digit operand.toList).2,
    Vector.length_toList,Nat.min_self]

theorem source_mul_add_rows_conserve_the_entire_original_accumulator_and_digit_product
    (operand accumulator : Vector UInt64 4) (digit : UInt64) :
    packWords (sourceMulAddRows operand accumulator digit).1 +
      radix64^5*(sourceMulAddRows operand accumulator digit).2.toNat =
        packWords accumulator.toList + digit.toNat*packWords operand.toList := by
  have highWidth : (0 :: sourceProductHighWords digit operand.toList).length = 5 := by
    rw [List.length_cons,
      (TransferBlstArmProducts01.source_product_vectors_retain_the_source_modulus_limb_count digit operand.toList).2,
      Vector.length_toList]
  have leftProjection : (sourceMulAddLowFive operand accumulator digit).length ≤
      (0 :: sourceProductHighWords digit operand.toList).length := by
    rw [source_mul_add_extended_low_phase_retains_five_words,highWidth]
  have rightProjection : (0 :: sourceProductHighWords digit operand.toList).length ≤
      (sourceMulAddLowFive operand accumulator digit).length := by
    rw [highWidth,source_mul_add_extended_low_phase_retains_five_words]
  have second := TransferBlstArmCarryChains01.symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    false ((sourceMulAddLowFive operand accumulator digit).zip (0 :: sourceProductHighWords digit operand.toList))
  rw [List.map_fst_zip leftProjection,List.map_snd_zip rightProjection,List.length_zip,
    source_mul_add_extended_low_phase_retains_five_words,highWidth,Nat.min_self,
    source_mul_add_extended_low_phase_derives_the_full_low_product_sum] at second
  have product := TransferBlstArmProducts01.symbolic_packed_low_and_high_product_vectors_conserve_the_full_product
    digit operand.toList
  change packWords (sourceMulAddRows operand accumulator digit).1 +
    radix64^5*(sourceMulAddRows operand accumulator digit).2.toNat =
      (packWords accumulator.toList + packWords (sourceProductLowWords digit operand.toList)) +
        (0 + radix64*packWords (sourceProductHighWords digit operand.toList)) + 0 at second
  simp only [Nat.zero_add,Nat.add_zero] at second
  calc
    _ = packWords accumulator.toList +
      (packWords (sourceProductLowWords digit operand.toList) + radix64*packWords (sourceProductHighWords digit operand.toList)) := by
      exact second.trans (Nat.add_assoc _ _ _)
    _ = _ := by rw [product]

theorem canonical_operand_and_bounded_prior_accumulator_derive_no_discarded_product_overflow
    (operand : CanonicalScalar) (accumulator : Vector UInt64 4) (digit : UInt64)
    (prior : packWords accumulator.toList < 2*nullifierModulus) :
    (sourceMulAddRows operand.words accumulator digit).2 = false ∧
      packWords (sourceMulAddRows operand.words accumulator digit).1 =
        packWords accumulator.toList + digit.toNat*packWords operand.words.toList := by
  have conserved := source_mul_add_rows_conserve_the_entire_original_accumulator_and_digit_product operand.words accumulator digit
  have productBound : digit.toNat*packWords operand.words.toList ≤ radix64*nullifierModulus :=
    Nat.mul_le_mul (Nat.le_of_lt digit.toNat_lt) (Nat.le_of_lt operand.canonical)
  have radixBound : 2*nullifierModulus + radix64*nullifierModulus < radix64^5 := by decide
  have fullBound : packWords accumulator.toList + digit.toNat*packWords operand.words.toList < radix64^5 := by omega
  have noOverflow : (sourceMulAddRows operand.words accumulator digit).2 = false := by
    cases flag : (sourceMulAddRows operand.words accumulator digit).2 with
    | false => rfl
    | true => rw [flag] at conserved; change _ + radix64^5*1 = _ at conserved; omega
  rw [noOverflow] at conserved
  change packWords (sourceMulAddRows operand.words accumulator digit).1 + radix64^5*0 = _ at conserved
  simp only [Nat.mul_zero,Nat.add_zero] at conserved
  exact ⟨noOverflow,conserved⟩
set_option pp.all true in
#check @sourceMulAddLowPhase
#print axioms sourceMulAddLowPhase
set_option pp.all true in
#check @source_mul_add_low_phase_retains_the_four_low_words
#print axioms source_mul_add_low_phase_retains_the_four_low_words
set_option pp.all true in
#check @boolean_carry_word_retains_the_exact_flag_integer
#print axioms boolean_carry_word_retains_the_exact_flag_integer
set_option pp.all true in
#check @sourceMulAddLowFive
#print axioms sourceMulAddLowFive
set_option pp.all true in
#check @source_mul_add_extended_low_phase_retains_five_words
#print axioms source_mul_add_extended_low_phase_retains_five_words
set_option pp.all true in
#check @source_mul_add_extended_low_phase_derives_the_full_low_product_sum
#print axioms source_mul_add_extended_low_phase_derives_the_full_low_product_sum
set_option pp.all true in
#check @sourceMulAddRows
#print axioms sourceMulAddRows
set_option pp.all true in
#check @source_mul_add_rows_retain_the_five_accumulator_words
#print axioms source_mul_add_rows_retain_the_five_accumulator_words
set_option pp.all true in
#check @source_mul_add_rows_conserve_the_entire_original_accumulator_and_digit_product
#print axioms source_mul_add_rows_conserve_the_entire_original_accumulator_and_digit_product
set_option pp.all true in
#check @canonical_operand_and_bounded_prior_accumulator_derive_no_discarded_product_overflow
#print axioms canonical_operand_and_bounded_prior_accumulator_derive_no_discarded_product_overflow
end ShielddSecurity.TransferBlstArmMulRows01
