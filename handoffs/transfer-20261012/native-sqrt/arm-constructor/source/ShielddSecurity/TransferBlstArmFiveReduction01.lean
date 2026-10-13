import ShielddSecurity.TransferBlstArmMulRows01
import ShielddSecurity.TransferBlstArmCancellation01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmFiveReduction01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarFourRoundWrapper01 (modulusWords)
open TransferBlstArmCancellation01
open TransferBlstArmCarryChains01
open TransferBlstArmProducts01
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceAddCarryChain sourceProductLowWords sourceProductHighWords sourceProductSplit

theorem two_plain_integer_carry_equations_compose_without_limb_expansion
    (span first second flagA flagB rest low carry high : Nat)
    (firstEquation : first+span*flagA=rest+low+carry)
    (secondEquation : second+span*flagB=first+high) :
    second+span*(flagA+flagB)=rest+low+carry+high := by
  rw [Nat.mul_add]
  omega

theorem plain_low_cancellation_and_product_split_derive_the_radix_factor
    (radix word lowWord rest lowTail highWords multiplier modulus carry : Nat)
    (productEquation : lowWord+radix*lowTail+radix*highWords=multiplier*modulus)
    (cancellation : radix*carry=word+lowWord) :
    word+radix*rest+multiplier*modulus=radix*(rest+lowTail+carry+highWords) := by
  rw [← productEquation]
  simp only [Nat.mul_add]
  omega

theorem nonnegative_flag_weight_below_its_span_forces_zero
    (span low flags quotient : Nat) (bounded : quotient<span)
    (equation : low+span*flags=quotient) : flags=0 := by
  by_contra nonzero
  have positive : 1 ≤ flags := Nat.one_le_iff_ne_zero.mpr nonzero
  have product := Nat.mul_le_mul_left span positive
  rw [Nat.mul_one] at product
  omega

theorem symbolic_low_product_vector_cons_retains_the_head_product
    (multiplier word : UInt64) (rest : List UInt64) :
    sourceProductLowWords multiplier (word::rest) =
      (sourceProductSplit multiplier word).1 :: sourceProductLowWords multiplier rest := by
  simp only [sourceProductLowWords,List.map_cons]

def sourceFiveLowProducts (word : UInt64) : List UInt64 :=
  sourceProductLowWords (sourceArmMultiplier word) (modulusWords.drop 1) ++ [0]

def sourceFiveFirstPass (word : UInt64) (rest : List UInt64) : List UInt64 × Bool :=
  sourceAddCarryChain (sourceArmSubsOneCarry word) (rest.zip (sourceFiveLowProducts word))

def sourceFiveSecondPass (word : UInt64) (rest : List UInt64) : List UInt64 × Bool :=
  sourceAddCarryChain false ((sourceFiveFirstPass word rest).1.zip
    (sourceProductHighWords (sourceArmMultiplier word) modulusWords))

attribute [local irreducible] sourceFiveLowProducts sourceFiveFirstPass sourceFiveSecondPass

theorem five_input_elimination_low_product_tail_retains_four_words (word : UInt64) :
    (sourceFiveLowProducts word).length = 4 := by
  rw [sourceFiveLowProducts,List.length_append,
    (source_product_vectors_retain_the_source_modulus_limb_count _ _).1,
    List.length_drop,TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs]
  rfl

theorem five_input_elimination_first_pass_retains_four_words
    (word : UInt64) (rest : List UInt64) (four : rest.length=4) :
    (sourceFiveFirstPass word rest).1.length=4 := by
  rw [sourceFiveFirstPass,actual_add_chain_retains_the_source_limb_count,List.length_zip,four,
    five_input_elimination_low_product_tail_retains_four_words,Nat.min_self]

theorem five_input_elimination_second_pass_retains_four_words
    (word : UInt64) (rest : List UInt64) (four : rest.length=4) :
    (sourceFiveSecondPass word rest).1.length=4 := by
  rw [sourceFiveSecondPass,actual_add_chain_retains_the_source_limb_count,List.length_zip,
    five_input_elimination_first_pass_retains_four_words _ _ four,
    (source_product_vectors_retain_the_source_modulus_limb_count _ _).2,
    TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs,Nat.min_self]

theorem appending_one_zero_word_retains_the_exact_packed_integer (words : List UInt64) :
    packWords (words++[0])=packWords words := by
  rw [TransferScalarCarrySchedule01.packing_append_preserves_positional_value]
  simp only [packWords,UInt64.toNat_zero,Nat.mul_zero,Nat.add_zero]

theorem five_input_first_pass_has_the_exact_integer_conservation_equation
    (word : UInt64) (rest : List UInt64) (four : rest.length=4) :
    packWords (sourceFiveFirstPass word rest).1+radix64^4*(sourceFiveFirstPass word rest).2.toNat =
      packWords rest+packWords (sourceProductLowWords (sourceArmMultiplier word) (modulusWords.drop 1))+
        (sourceArmSubsOneCarry word).toNat := by
  unfold sourceFiveFirstPass
  have lowWidth := five_input_elimination_low_product_tail_retains_four_words word
  have padding : packWords (sourceFiveLowProducts word) =
      packWords (sourceProductLowWords (sourceArmMultiplier word) (modulusWords.drop 1)) := by
    rw [sourceFiveLowProducts]
    exact appending_one_zero_word_retains_the_exact_packed_integer _
  have raw := symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    (sourceArmSubsOneCarry word) (rest.zip (sourceFiveLowProducts word))
  rw [List.map_fst_zip (by rw [four,lowWidth] : rest.length ≤ (sourceFiveLowProducts word).length),
    List.map_snd_zip (by rw [lowWidth,four] : (sourceFiveLowProducts word).length ≤ rest.length),
    List.length_zip,four,lowWidth,Nat.min_self,padding] at raw
  exact raw

theorem five_input_second_pass_has_the_exact_integer_conservation_equation
    (word : UInt64) (rest : List UInt64) (four : rest.length=4) :
    packWords (sourceFiveSecondPass word rest).1+radix64^4*(sourceFiveSecondPass word rest).2.toNat =
      packWords (sourceFiveFirstPass word rest).1+
        packWords (sourceProductHighWords (sourceArmMultiplier word) modulusWords) := by
  unfold sourceFiveSecondPass
  have firstWidth := five_input_elimination_first_pass_retains_four_words word rest four
  have highWidth : (sourceProductHighWords (sourceArmMultiplier word) modulusWords).length=4 :=
    (source_product_vectors_retain_the_source_modulus_limb_count _ _).2.trans
      TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs
  have raw := symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag false
    ((sourceFiveFirstPass word rest).1.zip (sourceProductHighWords (sourceArmMultiplier word) modulusWords))
  rw [List.map_fst_zip (by rw [firstWidth,highWidth] : (sourceFiveFirstPass word rest).1.length ≤
      (sourceProductHighWords (sourceArmMultiplier word) modulusWords).length),
    List.map_snd_zip (by rw [highWidth,firstWidth] : (sourceProductHighWords (sourceArmMultiplier word) modulusWords).length ≤
      (sourceFiveFirstPass word rest).1.length),
    List.length_zip,firstWidth,highWidth,Nat.min_self,Bool.toNat_false,Nat.add_zero] at raw
  exact raw

theorem five_input_elimination_original_numerator_has_the_derived_exact_radix_factor
    (word : UInt64) (rest : List UInt64) :
    packWords (word::rest)+(sourceArmMultiplier word).toNat*nullifierModulus =
      radix64*(packWords rest+
        packWords (sourceProductLowWords (sourceArmMultiplier word) (modulusWords.drop 1))+
        (sourceArmSubsOneCarry word).toNat+
        packWords (sourceProductHighWords (sourceArmMultiplier word) modulusWords)) := by
  have product := symbolic_packed_low_and_high_product_vectors_conserve_the_full_product (sourceArmMultiplier word) modulusWords
  rw [TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus] at product
  have modulusCons : modulusWords = sourceBlstPLow :: modulusWords.drop 1 := rfl
  have lowCons := (congrArg (sourceProductLowWords (sourceArmMultiplier word)) modulusCons).trans
    (symbolic_low_product_vector_cons_retains_the_head_product (sourceArmMultiplier word) sourceBlstPLow (modulusWords.drop 1))
  rw [lowCons] at product
  change (sourceProductSplit (sourceArmMultiplier word) sourceBlstPLow).1.toNat+
    radix64*packWords (sourceProductLowWords (sourceArmMultiplier word) (modulusWords.drop 1))+
    radix64*packWords (sourceProductHighWords (sourceArmMultiplier word) modulusWords) =
      (sourceArmMultiplier word).toNat*nullifierModulus at product
  rw [actual_product_low_word_is_the_source_wrapped_mul] at product
  have lowCancel := actual_arm_low_word_sum_has_zero_remainder_from_the_locked_multiplier word
  have lowSplit := Nat.mod_add_div (word.toNat+(sourceArmMultiplier word*sourceBlstPLow).toNat) radix64
  rw [lowCancel,Nat.zero_add,
    ← actual_arm_subs_one_flag_predicate_is_the_derived_montgomery_low_add_carry word] at lowSplit
  change word.toNat+radix64*packWords rest+(sourceArmMultiplier word).toNat*nullifierModulus = _
  exact plain_low_cancellation_and_product_split_derive_the_radix_factor
    radix64 word.toNat (sourceArmMultiplier word*sourceBlstPLow).toNat (packWords rest)
    (packWords (sourceProductLowWords (sourceArmMultiplier word) (modulusWords.drop 1)))
    (packWords (sourceProductHighWords (sourceArmMultiplier word) modulusWords))
    (sourceArmMultiplier word).toNat nullifierModulus (sourceArmSubsOneCarry word).toNat product lowSplit

theorem five_input_elimination_two_passes_retain_both_flags_in_the_exact_quotient_equation
    (word : UInt64) (rest : List UInt64) (four : rest.length=4) :
    packWords (sourceFiveSecondPass word rest).1 +
      radix64^4*((sourceFiveFirstPass word rest).2.toNat+(sourceFiveSecondPass word rest).2.toNat) =
        (packWords (word::rest)+(sourceArmMultiplier word).toNat*nullifierModulus)/radix64 := by
  have combined := two_plain_integer_carry_equations_compose_without_limb_expansion
    (radix64^4) (packWords (sourceFiveFirstPass word rest).1) (packWords (sourceFiveSecondPass word rest).1)
    (sourceFiveFirstPass word rest).2.toNat (sourceFiveSecondPass word rest).2.toNat
    (packWords rest) (packWords (sourceProductLowWords (sourceArmMultiplier word) (modulusWords.drop 1)))
    (sourceArmSubsOneCarry word).toNat (packWords (sourceProductHighWords (sourceArmMultiplier word) modulusWords))
    (five_input_first_pass_has_the_exact_integer_conservation_equation word rest four)
    (five_input_second_pass_has_the_exact_integer_conservation_equation word rest four)
  rw [five_input_elimination_original_numerator_has_the_derived_exact_radix_factor,
    Nat.mul_div_cancel_left _ (by decide : 0 < radix64)]
  exact combined

theorem bounded_five_input_elimination_derives_both_zero_flags_and_the_exact_quotient
    (word : UInt64) (rest : List UInt64) (four : rest.length=4)
    (bounded : (packWords (word::rest)+(sourceArmMultiplier word).toNat*nullifierModulus)/radix64 < radix64^4) :
    (sourceFiveFirstPass word rest).2=false ∧ (sourceFiveSecondPass word rest).2=false ∧
      packWords (sourceFiveSecondPass word rest).1 =
        (packWords (word::rest)+(sourceArmMultiplier word).toNat*nullifierModulus)/radix64 := by
  have equation := five_input_elimination_two_passes_retain_both_flags_in_the_exact_quotient_equation word rest four
  have flagsZero : (sourceFiveFirstPass word rest).2.toNat+(sourceFiveSecondPass word rest).2.toNat=0 :=
    nonnegative_flag_weight_below_its_span_forces_zero (radix64^4)
      (packWords (sourceFiveSecondPass word rest).1)
      ((sourceFiveFirstPass word rest).2.toNat+(sourceFiveSecondPass word rest).2.toNat)
      _ bounded equation
  have firstZero : (sourceFiveFirstPass word rest).2.toNat=0 := by omega
  have secondZero : (sourceFiveSecondPass word rest).2.toNat=0 := by omega
  rw [flagsZero,Nat.mul_zero,Nat.add_zero] at equation
  exact ⟨Bool.toNat_eq_zero.mp firstZero,Bool.toNat_eq_zero.mp secondZero,equation⟩
set_option pp.all true in
#check @two_plain_integer_carry_equations_compose_without_limb_expansion
#print axioms two_plain_integer_carry_equations_compose_without_limb_expansion
set_option pp.all true in
#check @plain_low_cancellation_and_product_split_derive_the_radix_factor
#print axioms plain_low_cancellation_and_product_split_derive_the_radix_factor
set_option pp.all true in
#check @nonnegative_flag_weight_below_its_span_forces_zero
#print axioms nonnegative_flag_weight_below_its_span_forces_zero
set_option pp.all true in
#check @symbolic_low_product_vector_cons_retains_the_head_product
#print axioms symbolic_low_product_vector_cons_retains_the_head_product
set_option pp.all true in
#check @sourceFiveLowProducts
#print axioms sourceFiveLowProducts
set_option pp.all true in
#check @sourceFiveFirstPass
#print axioms sourceFiveFirstPass
set_option pp.all true in
#check @sourceFiveSecondPass
#print axioms sourceFiveSecondPass
set_option pp.all true in
#check @five_input_elimination_low_product_tail_retains_four_words
#print axioms five_input_elimination_low_product_tail_retains_four_words
set_option pp.all true in
#check @five_input_elimination_first_pass_retains_four_words
#print axioms five_input_elimination_first_pass_retains_four_words
set_option pp.all true in
#check @five_input_elimination_second_pass_retains_four_words
#print axioms five_input_elimination_second_pass_retains_four_words
set_option pp.all true in
#check @appending_one_zero_word_retains_the_exact_packed_integer
#print axioms appending_one_zero_word_retains_the_exact_packed_integer
set_option pp.all true in
#check @five_input_first_pass_has_the_exact_integer_conservation_equation
#print axioms five_input_first_pass_has_the_exact_integer_conservation_equation
set_option pp.all true in
#check @five_input_second_pass_has_the_exact_integer_conservation_equation
#print axioms five_input_second_pass_has_the_exact_integer_conservation_equation
set_option pp.all true in
#check @five_input_elimination_original_numerator_has_the_derived_exact_radix_factor
#print axioms five_input_elimination_original_numerator_has_the_derived_exact_radix_factor
set_option pp.all true in
#check @five_input_elimination_two_passes_retain_both_flags_in_the_exact_quotient_equation
#print axioms five_input_elimination_two_passes_retain_both_flags_in_the_exact_quotient_equation
set_option pp.all true in
#check @bounded_five_input_elimination_derives_both_zero_flags_and_the_exact_quotient
#print axioms bounded_five_input_elimination_derives_both_zero_flags_and_the_exact_quotient
end ShielddSecurity.TransferBlstArmFiveReduction01
