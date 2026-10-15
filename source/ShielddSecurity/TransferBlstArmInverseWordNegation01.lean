import ShielddSecurity.TransferBlstArmInverseZeroFactorRows01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordNegation01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmCarryChains01 (sourceAddCarryChain)

/-! Symbolic word complement and add-one conservation for the original
signed multiplication input preparation. The final carry is an arithmetic
witness; this is not a theorem about compiled flag/register execution. -/

def sourceComplementWords (words : List UInt64) : List UInt64 := words.map (fun word => ~~~word)

def sourceNegatedWordsAndCarry (words : List UInt64) : List UInt64 × Bool :=
  sourceAddCarryChain true ((sourceComplementWords words).zip (List.replicate words.length (0 : UInt64)))

theorem any_number_of_zero_words_has_zero_entire_packed_value (count : Nat) :
    packWords (List.replicate count (0 : UInt64)) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ, packWords, UInt64.toNat_zero, ih, Nat.mul_zero, Nat.add_zero]

theorem the_entire_word_complement_plus_the_original_plus_one_equals_the_full_radix_power
    (words : List UInt64) :
    packWords (sourceComplementWords words) + packWords words + 1 = radix64 ^ words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    have first : (~~~word).toNat + word.toNat + 1 = radix64 := by
      rw [UInt64.toNat_not]
      have bound := word.toNat_lt
      change word.toNat < 18446744073709551616 at bound
      change 18446744073709551616 - 1 - word.toNat + word.toNat + 1 = 18446744073709551616
      omega
    change (~~~word).toNat + radix64 * packWords (sourceComplementWords rest) +
      (word.toNat + radix64 * packWords rest) + 1 = radix64 ^ (rest.length + 1)
    calc
      _ = ((~~~word).toNat + word.toNat + 1) +
          radix64 * (packWords (sourceComplementWords rest) + packWords rest) := by ring1
      _ = radix64 * (packWords (sourceComplementWords rest) + packWords rest + 1) := by rw [first]; ring1
      _ = radix64 * radix64 ^ rest.length := by rw [ih]
      _ = radix64 ^ (rest.length + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem original_complement_add_one_retains_the_source_word_count (words : List UInt64) :
    (sourceNegatedWordsAndCarry words).1.length = words.length := by
  rw [sourceNegatedWordsAndCarry, TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
    List.length_zip, sourceComplementWords, List.length_map, List.length_replicate, Nat.min_self]

theorem original_complement_add_one_conserves_the_entire_word_value_and_last_arithmetic_carry
    (words : List UInt64) :
    packWords (sourceNegatedWordsAndCarry words).1 +
      radix64 ^ words.length * (sourceNegatedWordsAndCarry words).2.toNat + packWords words = radix64 ^ words.length := by
  have complementLength : (sourceComplementWords words).length = words.length := by rw [sourceComplementWords, List.length_map]
  have leftProjection : (sourceComplementWords words).length ≤ (List.replicate words.length (0 : UInt64)).length := by
    rw [complementLength, List.length_replicate]
  have rightProjection : (List.replicate words.length (0 : UInt64)).length ≤ (sourceComplementWords words).length := by
    rw [complementLength, List.length_replicate]
  have conserved := TransferBlstArmCarryChains01.symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    true ((sourceComplementWords words).zip (List.replicate words.length (0 : UInt64)))
  rw [List.map_fst_zip leftProjection, List.map_snd_zip rightProjection, List.length_zip,
    complementLength, List.length_replicate, Nat.min_self,
    any_number_of_zero_words_has_zero_entire_packed_value, Nat.add_zero] at conserved
  change packWords (sourceNegatedWordsAndCarry words).1 +
    radix64 ^ words.length * (sourceNegatedWordsAndCarry words).2.toNat = packWords (sourceComplementWords words) + 1 at conserved
  rw [conserved]
  have entire := the_entire_word_complement_plus_the_original_plus_one_equals_the_full_radix_power words
  omega

theorem a_nonzero_entire_input_derives_zero_negation_carry_and_the_exact_radix_complement
    (words : List UInt64) (nonzero : 0 < packWords words) :
    (sourceNegatedWordsAndCarry words).2 = false ∧
      packWords (sourceNegatedWordsAndCarry words).1 = radix64 ^ words.length - packWords words := by
  have entire := original_complement_add_one_conserves_the_entire_word_value_and_last_arithmetic_carry words
  cases carry : (sourceNegatedWordsAndCarry words).2
  · rw [carry] at entire
    change packWords (sourceNegatedWordsAndCarry words).1 + radix64 ^ words.length * 0 + packWords words = radix64 ^ words.length at entire
    refine ⟨rfl, ?_⟩
    omega
  · rw [carry] at entire
    change packWords (sourceNegatedWordsAndCarry words).1 + radix64 ^ words.length * 1 + packWords words = radix64 ^ words.length at entire
    omega

theorem a_zero_entire_input_derives_zero_negated_words_and_a_set_arithmetic_carry
    (words : List UInt64) (zero : packWords words = 0) :
    packWords (sourceNegatedWordsAndCarry words).1 = 0 ∧ (sourceNegatedWordsAndCarry words).2 = true := by
  have entire := original_complement_add_one_conserves_the_entire_word_value_and_last_arithmetic_carry words
  have bounded := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (sourceNegatedWordsAndCarry words).1
  rw [original_complement_add_one_retains_the_source_word_count] at bounded
  rw [zero] at entire
  cases carry : (sourceNegatedWordsAndCarry words).2
  · rw [carry] at entire
    change packWords (sourceNegatedWordsAndCarry words).1 + radix64 ^ words.length * 0 + 0 = radix64 ^ words.length at entire
    omega
  · rw [carry] at entire
    change packWords (sourceNegatedWordsAndCarry words).1 + radix64 ^ words.length * 1 + 0 = radix64 ^ words.length at entire
    refine ⟨?_, rfl⟩
    omega

set_option pp.all true in
#check @sourceComplementWords
#print axioms sourceComplementWords
set_option pp.all true in
#check @sourceNegatedWordsAndCarry
#print axioms sourceNegatedWordsAndCarry
set_option pp.all true in
#check @any_number_of_zero_words_has_zero_entire_packed_value
#print axioms any_number_of_zero_words_has_zero_entire_packed_value
set_option pp.all true in
#check @the_entire_word_complement_plus_the_original_plus_one_equals_the_full_radix_power
#print axioms the_entire_word_complement_plus_the_original_plus_one_equals_the_full_radix_power
set_option pp.all true in
#check @original_complement_add_one_retains_the_source_word_count
#print axioms original_complement_add_one_retains_the_source_word_count
set_option pp.all true in
#check @original_complement_add_one_conserves_the_entire_word_value_and_last_arithmetic_carry
#print axioms original_complement_add_one_conserves_the_entire_word_value_and_last_arithmetic_carry
set_option pp.all true in
#check @a_nonzero_entire_input_derives_zero_negation_carry_and_the_exact_radix_complement
#print axioms a_nonzero_entire_input_derives_zero_negation_carry_and_the_exact_radix_complement
set_option pp.all true in
#check @a_zero_entire_input_derives_zero_negated_words_and_a_set_arithmetic_carry
#print axioms a_zero_entire_input_derives_zero_negated_words_and_a_set_arithmetic_carry
end ShielddSecurity.TransferBlstArmInverseWordNegation01
