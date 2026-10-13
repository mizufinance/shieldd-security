import ShielddSecurity.TransferBlstArmCancellation01
import ShielddSecurity.TransferBlstArmProducts01
import ShielddSecurity.TransferBlstArmCarryChains01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmRound01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarFourRoundWrapper01 (modulusWords)
open TransferBlstArmCancellation01
open TransferBlstArmCarryChains01
open TransferBlstArmProducts01

def sourceFirstAdditionPass (word : UInt64) (rest : List UInt64) : List UInt64 × Bool :=
  sourceAddCarryChain (sourceArmSubsOneCarry word)
    (rest.zip (sourceProductLowWords (sourceArmMultiplier word) (modulusWords.drop 1)))

def sourceSecondAdditionInput (word : UInt64) (rest : List UInt64) : List UInt64 :=
  let first := sourceFirstAdditionPass word rest
  first.1 ++ [UInt64.ofNat first.2.toNat]

def sourceSecondAdditionPass (word : UInt64) (rest : List UInt64) : List UInt64 × Bool :=
  sourceAddCarryChain false ((sourceSecondAdditionInput word rest).zip
    (sourceProductHighWords (sourceArmMultiplier word) modulusWords))

theorem actual_source_first_pass_preserves_three_tail_limbs
    (word : UInt64) (rest : List UInt64) (three : rest.length = 3) :
    (sourceFirstAdditionPass word rest).1.length = 3 := by
  rw [sourceFirstAdditionPass,actual_add_chain_retains_the_source_limb_count,List.length_zip,three,
    sourceProductLowWords,List.length_map]
  rfl

theorem actual_source_second_pass_input_has_four_limbs
    (word : UInt64) (rest : List UInt64) (three : rest.length = 3) :
    (sourceSecondAdditionInput word rest).length = 4 := by
  rw [sourceSecondAdditionInput,List.length_append,actual_source_first_pass_preserves_three_tail_limbs word rest three]
  rfl

theorem actual_source_second_pass_preserves_four_output_limbs
    (word : UInt64) (rest : List UInt64) (three : rest.length = 3) :
    (sourceSecondAdditionPass word rest).1.length = 4 := by
  rw [sourceSecondAdditionPass,actual_add_chain_retains_the_source_limb_count,List.length_zip,
    actual_source_second_pass_input_has_four_limbs word rest three,sourceProductHighWords,List.length_map]
  rfl

theorem symbolic_actual_two_addition_passes_derive_the_montgomery_quotient
    (word : UInt64) (rest : List UInt64) (three : rest.length = 3) :
    packWords (sourceSecondAdditionPass word rest).1+
      radix64^4*(sourceSecondAdditionPass word rest).2.toNat =
      (packWords (word::rest)+(sourceArmMultiplier word).toNat*
        TransferBoundedNativeCodec01.nullifierModulus)/radix64 := by
  let multiplier := sourceArmMultiplier word
  let lowTail := sourceProductLowWords multiplier (modulusWords.drop 1)
  let highWords := sourceProductHighWords multiplier modulusWords
  let first := sourceFirstAdditionPass word rest
  let secondInput := sourceSecondAdditionInput word rest
  let second := sourceSecondAdditionPass word rest
  have lowWidth : lowTail.length = 3 := by
    change (sourceProductLowWords multiplier (modulusWords.drop 1)).length = 3
    rw [sourceProductLowWords,List.length_map]
    rfl
  have highWidth : highWords.length = 4 := by
    change (sourceProductHighWords multiplier modulusWords).length = 4
    rw [sourceProductHighWords,List.length_map]
    rfl
  have firstInteger := symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    (sourceArmSubsOneCarry word) (rest.zip lowTail)
  rw [List.map_fst_zip (by omega : rest.length ≤ lowTail.length),
    List.map_snd_zip (by omega : lowTail.length ≤ rest.length),
    List.length_zip,three,lowWidth,Nat.min_self] at firstInteger
  change packWords first.1+radix64^3*first.2.toNat =
    packWords rest+packWords lowTail+(sourceArmSubsOneCarry word).toNat at firstInteger
  have inputWidth : secondInput.length = 4 := actual_source_second_pass_input_has_four_limbs word rest three
  have secondInteger := symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    false (secondInput.zip highWords)
  rw [List.map_fst_zip (by omega : secondInput.length ≤ highWords.length),
    List.map_snd_zip (by omega : highWords.length ≤ secondInput.length),
    List.length_zip,inputWidth,highWidth,Nat.min_self, Bool.toNat_false,Nat.add_zero] at secondInteger
  change packWords second.1+radix64^4*second.2.toNat = packWords secondInput+packWords highWords at secondInteger
  have firstWidth : first.1.length=3 := actual_source_first_pass_preserves_three_tail_limbs word rest three
  have flagWord : (UInt64.ofNat first.2.toNat).toNat = first.2.toNat := by cases first.2 <;> rfl
  have inputInteger : packWords secondInput = packWords first.1+radix64^3*first.2.toNat := by
    change packWords (first.1 ++ [UInt64.ofNat first.2.toNat]) = _
    rw [TransferScalarCarrySchedule01.packing_append_preserves_positional_value,firstWidth]
    change packWords first.1+radix64^3*((UInt64.ofNat first.2.toNat).toNat+radix64*0) = _
    rw [flagWord,Nat.mul_zero,Nat.add_zero]
  rw [inputInteger,firstInteger] at secondInteger
  have product := symbolic_packed_low_and_high_product_vectors_conserve_the_full_product multiplier modulusWords
  rw [TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus] at product
  change (sourceProductSplit multiplier sourceBlstPLow).1.toNat+
      radix64*packWords lowTail+radix64*packWords highWords =
      multiplier.toNat*TransferBoundedNativeCodec01.nullifierModulus at product
  rw [actual_product_low_word_is_the_source_wrapped_mul] at product
  have lowCancel := actual_arm_low_word_sum_has_zero_remainder_from_the_locked_multiplier word
  have lowSplit := Nat.mod_add_div
    (word.toNat+(sourceArmMultiplier word*sourceBlstPLow).toNat) radix64
  rw [lowCancel,Nat.zero_add,
    ← actual_arm_subs_one_flag_predicate_is_the_derived_montgomery_low_add_carry word] at lowSplit
  have numerator : packWords (word::rest)+multiplier.toNat*TransferBoundedNativeCodec01.nullifierModulus =
      radix64*(packWords rest+packWords lowTail+(sourceArmSubsOneCarry word).toNat+packWords highWords) := by
    rw [← product]
    change word.toNat+radix64*packWords rest+
      ((sourceArmMultiplier word*sourceBlstPLow).toNat+radix64*packWords lowTail+radix64*packWords highWords) = _
    calc
      _ = (word.toNat+(sourceArmMultiplier word*sourceBlstPLow).toNat)+
          radix64*(packWords rest+packWords lowTail+packWords highWords) := by ring
      _ = _ := by rw [← lowSplit]; ring
  rw [numerator,Nat.mul_div_cancel_left _ (by decide : 0 < radix64)]
  exact secondInteger
set_option pp.all true in
#check @sourceFirstAdditionPass
#print axioms sourceFirstAdditionPass
set_option pp.all true in
#check @sourceSecondAdditionInput
#print axioms sourceSecondAdditionInput
set_option pp.all true in
#check @sourceSecondAdditionPass
#print axioms sourceSecondAdditionPass
set_option pp.all true in
#check @actual_source_first_pass_preserves_three_tail_limbs
#print axioms actual_source_first_pass_preserves_three_tail_limbs
set_option pp.all true in
#check @actual_source_second_pass_input_has_four_limbs
#print axioms actual_source_second_pass_input_has_four_limbs
set_option pp.all true in
#check @actual_source_second_pass_preserves_four_output_limbs
#print axioms actual_source_second_pass_preserves_four_output_limbs
set_option pp.all true in
#check @symbolic_actual_two_addition_passes_derive_the_montgomery_quotient
#print axioms symbolic_actual_two_addition_passes_derive_the_montgomery_quotient
end ShielddSecurity.TransferBlstArmRound01
