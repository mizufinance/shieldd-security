import ShielddSecurity.TransferScalarCarrySchedule01
import Init.Data.List.Zip
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarFourRoundWrapper01
open TransferScalarSerializationRange01 (radix64 reduceRounds normalize)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarCarrySchedule01 (macLoop dropLowAndAppendCarry)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Four-round finite carry wrapper derived from pinned Scalar source constants.
Each actual model multiplier is the wrapping UInt64 product of the current low
word and INV. The carry walk, low-word drop and retained carry derive the Nat
quotient recurrence. The canonical range follows from finite raw UInt64 input;
no input-field-range or caller-provided multiplier list premise is supplied.
Source shape/identity is separate from Rust primitive/ADC/SBB/byte/trace
correspondence; top zero limbs in to_bytes motivate carry appending here. -/
def modulusWords : List UInt64 := [0xffff_ffff_0000_0001, 0x53bd_a402_fffe_5bfe, 0x3339_d808_09a1_d805, 0x73ed_a753_299d_7d48]
def inverseWord : UInt64 := 0xffff_fffe_ffff_ffff
def nativeRound (words : List UInt64) : List UInt64 :=
  dropLowAndAppendCarry (macLoop (words.headD 0 * inverseWord) 0 (words.zip modulusWords))
def nativeRounds : Nat → List UInt64 → List UInt64
  | 0, words => words
  | rounds + 1, words => nativeRounds rounds (nativeRound words)
def roundMultipliers : Nat → List UInt64 → List Nat
  | 0, _ => []
  | rounds + 1, words => (words.headD 0 * inverseWord).toNat :: roundMultipliers rounds (nativeRound words)

theorem modulus_words_have_four_limbs : modulusWords.length = 4 := rfl
theorem modulus_words_pack_to_actual_nullifier_modulus : packWords modulusWords = nullifierModulus := by decide

theorem one_native_round_preserves_four_word_width (words : List UInt64) (four : words.length = 4) :
    (nativeRound words).length = 4 := by
  have zipped : (words.zip modulusWords).length = 4 := by
    rw [List.length_zip, four, modulus_words_have_four_limbs, Nat.min_self]
  change ((macLoop (words.headD 0 * inverseWord) 0 (words.zip modulusWords)).1.drop 1 ++
    [(macLoop (words.headD 0 * inverseWord) 0 (words.zip modulusWords)).2]).length = 4
  rw [List.length_append, List.length_drop, TransferScalarCarrySchedule01.carry_walk_retains_limb_count,
    zipped]
  rfl

theorem one_native_round_packs_to_derived_radix_quotient (words : List UInt64) (four : words.length = 4) :
    packWords (nativeRound words) =
      (packWords words + (words.headD 0 * inverseWord).toNat * nullifierModulus) / radix64 := by
  have zipped : (words.zip modulusWords).length = 4 := by
    rw [List.length_zip, four, modulus_words_have_four_limbs, Nat.min_self]
  have nonempty : words.zip modulusWords ≠ [] := by
    intro empty
    rw [empty, List.length_nil] at zipped
    cases zipped
  have firstProjection : words.length ≤ modulusWords.length := by
    rw [four, modulus_words_have_four_limbs]
    exact Nat.le_refl 4
  have secondProjection : modulusWords.length ≤ words.length := by
    rw [four, modulus_words_have_four_limbs]
    exact Nat.le_refl 4
  have result := TransferScalarCarrySchedule01.nonempty_mac_walk_drops_to_exact_quotient
    (words.headD 0 * inverseWord) 0 (words.zip modulusWords) nonempty
  rw [List.map_fst_zip firstProjection, List.map_snd_zip secondProjection,
    modulus_words_pack_to_actual_nullifier_modulus, UInt64.toNat_zero, Nat.add_zero] at result
  exact result

theorem native_round_walk_preserves_four_word_width (rounds : Nat) (words : List UInt64)
    (four : words.length = 4) : (nativeRounds rounds words).length = 4 := by
  induction rounds generalizing words with
  | zero => exact four
  | succ rounds ih => exact ih (nativeRound words) (one_native_round_preserves_four_word_width words four)

theorem derived_multiplier_vector_has_round_count (rounds : Nat) (words : List UInt64) :
    (roundMultipliers rounds words).length = rounds := by
  induction rounds generalizing words with
  | zero => rfl
  | succ rounds ih =>
    change (roundMultipliers rounds (nativeRound words)).length + 1 = rounds + 1
    rw [ih]

theorem every_derived_multiplier_is_a_finite_u64_word (rounds : Nat) (words : List UInt64) :
    ∀ digit ∈ roundMultipliers rounds words, digit < radix64 := by
  induction rounds generalizing words with
  | zero => intro digit inside; cases inside
  | succ rounds ih =>
    intro digit inside
    cases inside with
    | head => exact (words.headD 0 * inverseWord).toNat_lt
    | tail _ inside => exact ih (nativeRound words) digit inside

theorem native_carry_rounds_pack_to_symbolic_reduction (rounds : Nat) (words : List UInt64)
    (four : words.length = 4) :
    packWords (nativeRounds rounds words) =
      reduceRounds nullifierModulus radix64 (packWords words) (roundMultipliers rounds words) := by
  induction rounds generalizing words with
  | zero => rfl
  | succ rounds ih =>
    change packWords (nativeRounds rounds (nativeRound words)) =
      reduceRounds nullifierModulus radix64
        ((packWords words + (words.headD 0 * inverseWord).toNat * nullifierModulus) / radix64)
        (roundMultipliers rounds (nativeRound words))
    rw [← one_native_round_packs_to_derived_radix_quotient words four]
    exact ih (nativeRound words) (one_native_round_preserves_four_word_width words four)

theorem actual_four_round_carry_wrapper_normalizes_into_canonical_nullifier_field
    (words : List UInt64) (four : words.length = 4) :
    normalize nullifierModulus (packWords (nativeRounds 4 words)) < nullifierModulus := by
  apply TransferScalarSerializationRange01.final_subtraction_is_canonical nullifierModulus _ (by decide)
  rw [native_carry_rounds_pack_to_symbolic_reduction 4 words four]
  apply TransferScalarSerializationRange01.all_rounds_finish_at_most_modulus nullifierModulus radix64
    (roundMultipliers 4 words) (by decide) (every_derived_multiplier_is_a_finite_u64_word 4 words)
  rw [derived_multiplier_vector_has_round_count]
  have raw := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power words
  rw [four] at raw
  exact Nat.lt_of_lt_of_le raw (Nat.le_add_left _ _)

set_option pp.all true in
#check @modulusWords
#print axioms modulusWords
set_option pp.all true in
#check @inverseWord
#print axioms inverseWord
set_option pp.all true in
#check @nativeRound
#print axioms nativeRound
set_option pp.all true in
#check @nativeRounds
#print axioms nativeRounds
set_option pp.all true in
#check @roundMultipliers
#print axioms roundMultipliers
set_option pp.all true in
#check @modulus_words_have_four_limbs
#print axioms modulus_words_have_four_limbs
set_option pp.all true in
#check @modulus_words_pack_to_actual_nullifier_modulus
#print axioms modulus_words_pack_to_actual_nullifier_modulus
set_option pp.all true in
#check @one_native_round_preserves_four_word_width
#print axioms one_native_round_preserves_four_word_width
set_option pp.all true in
#check @one_native_round_packs_to_derived_radix_quotient
#print axioms one_native_round_packs_to_derived_radix_quotient
set_option pp.all true in
#check @native_round_walk_preserves_four_word_width
#print axioms native_round_walk_preserves_four_word_width
set_option pp.all true in
#check @derived_multiplier_vector_has_round_count
#print axioms derived_multiplier_vector_has_round_count
set_option pp.all true in
#check @every_derived_multiplier_is_a_finite_u64_word
#print axioms every_derived_multiplier_is_a_finite_u64_word
set_option pp.all true in
#check @native_carry_rounds_pack_to_symbolic_reduction
#print axioms native_carry_rounds_pack_to_symbolic_reduction
set_option pp.all true in
#check @actual_four_round_carry_wrapper_normalizes_into_canonical_nullifier_field
#print axioms actual_four_round_carry_wrapper_normalizes_into_canonical_nullifier_field
end ShielddSecurity.TransferScalarFourRoundWrapper01
