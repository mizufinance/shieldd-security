import ShielddSecurity.TransferBlstArmRound01
import ShielddSecurity.TransferCanonicalWordEquality01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmReduction01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarFourRoundWrapper01 (nativeRound nativeRounds)
open TransferBlstArmCancellation01
open TransferBlstArmRound01

theorem actual_source_second_pass_final_overflow_flag_is_false
    (word : UInt64) (rest : List UInt64) (three : rest.length = 3) :
    (sourceSecondAdditionPass word rest).2 = false := by
  have four : (word::rest).length = 4 := by simp only [List.length_cons,three]
  have bound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (nativeRound (word::rest))
  rw [TransferScalarFourRoundWrapper01.one_native_round_preserves_four_word_width _ four,
    TransferScalarFourRoundWrapper01.one_native_round_packs_to_derived_radix_quotient _ four,List.headD_cons] at bound
  have quotientBound :
      (packWords (word::rest)+(sourceArmMultiplier word).toNat*TransferBoundedNativeCodec01.nullifierModulus)/radix64 < radix64^4 := by
    rw [actual_arm_wrapped_multiplier_has_the_qualified_low_word_value]
    exact bound
  have equation := symbolic_actual_two_addition_passes_derive_the_montgomery_quotient word rest three
  cases flag : (sourceSecondAdditionPass word rest).2 with
  | false => rfl
  | true =>
    rw [flag,Bool.toNat_true,Nat.mul_one] at equation
    have impossible : radix64^4 ≤
        (packWords (word::rest)+(sourceArmMultiplier word).toNat*TransferBoundedNativeCodec01.nullifierModulus)/radix64 := by omega
    exact False.elim ((Nat.not_le_of_lt quotientBound) impossible)

def sourceArmReductionRound : List UInt64 → List UInt64
  | [] => []
  | word::rest => (sourceSecondAdditionPass word rest).1

theorem actual_arm_round_retains_the_four_limb_width (words : List UInt64) (four : words.length=4) :
    (sourceArmReductionRound words).length = 4 := by
  cases words with
  | nil => simp only [List.length_nil] at four; omega
  | cons word rest =>
    exact actual_source_second_pass_preserves_four_output_limbs word rest (by simp only [List.length_cons] at four; omega)

theorem actual_arm_round_derives_the_same_integer_as_the_qualified_word_round
    (words : List UInt64) (four : words.length=4) :
    packWords (sourceArmReductionRound words) = packWords (nativeRound words) := by
  cases words with
  | nil => simp only [List.length_nil] at four; omega
  | cons word rest =>
    have three : rest.length=3 := by simp only [List.length_cons] at four; omega
    have equation := symbolic_actual_two_addition_passes_derive_the_montgomery_quotient word rest three
    rw [actual_source_second_pass_final_overflow_flag_is_false word rest three,
      Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at equation
    rw [TransferScalarFourRoundWrapper01.one_native_round_packs_to_derived_radix_quotient _ four,List.headD_cons]
    rw [← actual_arm_wrapped_multiplier_has_the_qualified_low_word_value]
    exact equation

theorem actual_arm_round_derives_every_word_of_the_qualified_word_round
    (words : List UInt64) (four : words.length=4) : sourceArmReductionRound words = nativeRound words := by
  apply TransferCanonicalWordEquality01.equal_width_packed_u64_lists_are_equal
  · rw [actual_arm_round_retains_the_four_limb_width words four,
      TransferScalarFourRoundWrapper01.one_native_round_preserves_four_word_width words four]
  · exact actual_arm_round_derives_the_same_integer_as_the_qualified_word_round words four

def sourceArmReductionRounds : Nat → List UInt64 → List UInt64
  | 0, words => words
  | count+1, words => sourceArmReductionRounds count (sourceArmReductionRound words)

theorem symbolic_actual_arm_reduction_rounds_equal_the_qualified_word_recurrence
    (count : Nat) (words : List UInt64) (four : words.length=4) :
    sourceArmReductionRounds count words = nativeRounds count words := by
  induction count generalizing words with
  | zero => rfl
  | succ count ih =>
    change sourceArmReductionRounds count (sourceArmReductionRound words) = nativeRounds count (nativeRound words)
    rw [actual_arm_round_derives_every_word_of_the_qualified_word_round words four]
    exact ih _ (TransferScalarFourRoundWrapper01.one_native_round_preserves_four_word_width words four)
set_option pp.all true in
#check @actual_source_second_pass_final_overflow_flag_is_false
#print axioms actual_source_second_pass_final_overflow_flag_is_false
set_option pp.all true in
#check @sourceArmReductionRound
#print axioms sourceArmReductionRound
set_option pp.all true in
#check @actual_arm_round_retains_the_four_limb_width
#print axioms actual_arm_round_retains_the_four_limb_width
set_option pp.all true in
#check @actual_arm_round_derives_the_same_integer_as_the_qualified_word_round
#print axioms actual_arm_round_derives_the_same_integer_as_the_qualified_word_round
set_option pp.all true in
#check @actual_arm_round_derives_every_word_of_the_qualified_word_round
#print axioms actual_arm_round_derives_every_word_of_the_qualified_word_round
set_option pp.all true in
#check @sourceArmReductionRounds
#print axioms sourceArmReductionRounds
set_option pp.all true in
#check @symbolic_actual_arm_reduction_rounds_equal_the_qualified_word_recurrence
#print axioms symbolic_actual_arm_reduction_rounds_equal_the_qualified_word_recurrence
end ShielddSecurity.TransferBlstArmReduction01
