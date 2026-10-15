import ShielddSecurity.TransferScalarLittleEndianBytes01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarMontgomeryValue01
open TransferScalarSerializationRange01 (radix64 normalize)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarFourRoundWrapper01 (modulusWords inverseWord nativeRound nativeRounds)
open TransferScalarMaskedNormalization01 (sourceNormalize)
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes scalarKey)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Exact modular value of the finite source-shaped Montgomery serializer.
Source INV cancellation is proved as a closed integer certificate, then lifted
to all finite UInt64 low words. Small reusable lemmas and a symbolic round
induction derive the radix-power relation. Normalization and typed LE encoding
retain that relation; a kernel-checked constant radix inverse gives the exact
canonical mathematical projection. Rust primitive/trace/type interpretation
correspondence remains separate. No caller-provided cancellation or desired
output premise, no primality or curve replay, no wide unrolled constraints. -/

def radixInverse : Nat := 12549076656233958353659347336803947287922716146853412054870763148006372261952

def montgomeryValue (words : Vector UInt64 4) : Nat :=
  radixInverse * packWords words.toList % nullifierModulus

theorem source_inverse_word_cancels_modulus_low_word :
    (1 + inverseWord.toNat * (modulusWords.headD 0).toNat) % radix64 = 0 := by decide

theorem packed_vector_modulo_radix_is_actual_low_word (words : List UInt64) :
    packWords words % radix64 = (words.headD 0).toNat := by
  cases words with
  | nil => rfl
  | cons word rest =>
    change (word.toNat + radix64 * packWords rest) % radix64 = word.toNat
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt word.toNat_lt

theorem source_modulus_modulo_radix_is_actual_low_word :
    nullifierModulus % radix64 = (modulusWords.headD 0).toNat := by
  rw [← TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus]
  exact packed_vector_modulo_radix_is_actual_low_word modulusWords

theorem wrapped_source_multiplier_cancels_any_low_word (word : UInt64) :
    (word.toNat + (word * inverseWord).toNat * (modulusWords.headD 0).toNat) % radix64 = 0 := by
  rw [UInt64.toNat_mul]
  change (word.toNat + (word.toNat * inverseWord.toNat % radix64) * (modulusWords.headD 0).toNat) % radix64 = 0
  have wordBound : word.toNat < radix64 := word.toNat_lt
  rw [Nat.add_mod, Nat.mod_mul_mod, Nat.mod_eq_of_lt wordBound, Nat.add_mod_mod]
  have factored : word.toNat + word.toNat * inverseWord.toNat * (modulusWords.headD 0).toNat =
      word.toNat * (1 + inverseWord.toNat * (modulusWords.headD 0).toNat) := by
    rw [Nat.mul_add, Nat.mul_one]
    ac_rfl
  rw [factored, Nat.mul_mod, source_inverse_word_cancels_modulus_low_word, Nat.mul_zero, Nat.zero_mod]

theorem derived_round_numerator_is_divisible_by_radix (words : List UInt64) :
    (packWords words + (words.headD 0 * inverseWord).toNat * nullifierModulus) % radix64 = 0 := by
  have finite : (words.headD 0 * inverseWord).toNat < radix64 := (words.headD 0 * inverseWord).toNat_lt
  rw [Nat.add_mod, Nat.mul_mod, packed_vector_modulo_radix_is_actual_low_word,
    source_modulus_modulo_radix_is_actual_low_word, Nat.mod_eq_of_lt finite, Nat.add_mod_mod]
  exact wrapped_source_multiplier_cancels_any_low_word (words.headD 0)

theorem native_round_has_exact_montgomery_integer_equation (words : List UInt64) (four : words.length = 4) :
    radix64 * packWords (nativeRound words) =
      packWords words + (words.headD 0 * inverseWord).toNat * nullifierModulus := by
  rw [TransferScalarFourRoundWrapper01.one_native_round_packs_to_derived_radix_quotient words four]
  have exactDivision := Nat.mod_add_div
    (packWords words + (words.headD 0 * inverseWord).toNat * nullifierModulus) radix64
  rw [derived_round_numerator_is_divisible_by_radix, Nat.zero_add] at exactDivision
  exact exactDivision

theorem symbolic_native_round_walk_preserves_montgomery_modular_value
    (rounds : Nat) (words : List UInt64) (four : words.length = 4) :
    (radix64 ^ rounds * packWords (nativeRounds rounds words)) % nullifierModulus =
      packWords words % nullifierModulus := by
  induction rounds generalizing words with
  | zero => simp only [Nat.pow_zero, nativeRounds, Nat.one_mul]
  | succ rounds ih =>
    change (radix64 ^ (rounds + 1) * packWords (nativeRounds rounds (nativeRound words))) % nullifierModulus = _
    have reassoc : radix64 ^ (rounds + 1) * packWords (nativeRounds rounds (nativeRound words)) =
        radix64 * (radix64 ^ rounds * packWords (nativeRounds rounds (nativeRound words))) := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [reassoc, Nat.mul_mod, ih (nativeRound words)
      (TransferScalarFourRoundWrapper01.one_native_round_preserves_four_word_width words four),
      ← Nat.mul_mod, native_round_has_exact_montgomery_integer_equation words four,
      Nat.add_mul_mod_self_right]

theorem single_modulus_normalization_preserves_modular_value (value : Nat) :
    normalize nullifierModulus value % nullifierModulus = value % nullifierModulus := by
  by_cases enough : nullifierModulus ≤ value
  · rw [normalize, if_pos enough]
    have restored := congrArg (fun v => v % nullifierModulus) (Nat.sub_add_cancel enough)
    change (value - nullifierModulus + nullifierModulus) % nullifierModulus = value % nullifierModulus at restored
    rw [Nat.add_mod_right] at restored
    exact restored
  · rw [normalize, if_neg enough]

theorem typed_source_serializer_preserves_four_round_montgomery_relation
    (words : List UInt64) (four : words.length = 4) :
    (radix64 ^ 4 * decodeLE (serializerBytes words)) % nullifierModulus =
      packWords words % nullifierModulus := by
  unfold serializerBytes
  rw [TransferScalarLittleEndianBytes01.serialized_word_vector_reconstructs_actual_packed_words,
    TransferScalarMaskedNormalization01.source_sub_and_masked_addback_equal_single_modulus_normalization _
      (TransferScalarFourRoundWrapper01.native_round_walk_preserves_four_word_width 4 words four),
    Nat.mul_mod, single_modulus_normalization_preserves_modular_value, ← Nat.mul_mod]
  exact symbolic_native_round_walk_preserves_montgomery_modular_value 4 words four

theorem source_four_word_radix_inverse_is_exact :
    (radixInverse * radix64 ^ 4) % nullifierModulus = 1 := by decide

theorem fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value (words : Vector UInt64 4) :
    scalarKey words = montgomeryValue words := by
  have relation := typed_source_serializer_preserves_four_round_montgomery_relation words.toList Vector.length_toList
  change (radix64 ^ 4 * scalarKey words) % nullifierModulus = packWords words.toList % nullifierModulus at relation
  have scaled := congrArg (fun value => radixInverse * value % nullifierModulus) relation
  simp only [Nat.mul_mod_mod] at scaled
  rw [← Nat.mul_assoc, Nat.mul_mod, source_four_word_radix_inverse_is_exact,
    Nat.one_mul, Nat.mod_mod,
    Nat.mod_eq_of_lt (TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical words)] at scaled
  exact scaled

set_option pp.all true in
#check @radixInverse
#print axioms radixInverse
set_option pp.all true in
#check @montgomeryValue
#print axioms montgomeryValue
set_option pp.all true in
#check @source_inverse_word_cancels_modulus_low_word
#print axioms source_inverse_word_cancels_modulus_low_word
set_option pp.all true in
#check @packed_vector_modulo_radix_is_actual_low_word
#print axioms packed_vector_modulo_radix_is_actual_low_word
set_option pp.all true in
#check @source_modulus_modulo_radix_is_actual_low_word
#print axioms source_modulus_modulo_radix_is_actual_low_word
set_option pp.all true in
#check @wrapped_source_multiplier_cancels_any_low_word
#print axioms wrapped_source_multiplier_cancels_any_low_word
set_option pp.all true in
#check @derived_round_numerator_is_divisible_by_radix
#print axioms derived_round_numerator_is_divisible_by_radix
set_option pp.all true in
#check @native_round_has_exact_montgomery_integer_equation
#print axioms native_round_has_exact_montgomery_integer_equation
set_option pp.all true in
#check @symbolic_native_round_walk_preserves_montgomery_modular_value
#print axioms symbolic_native_round_walk_preserves_montgomery_modular_value
set_option pp.all true in
#check @single_modulus_normalization_preserves_modular_value
#print axioms single_modulus_normalization_preserves_modular_value
set_option pp.all true in
#check @typed_source_serializer_preserves_four_round_montgomery_relation
#print axioms typed_source_serializer_preserves_four_round_montgomery_relation
set_option pp.all true in
#check @source_four_word_radix_inverse_is_exact
#print axioms source_four_word_radix_inverse_is_exact
set_option pp.all true in
#check @fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value
#print axioms fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value
end ShielddSecurity.TransferScalarMontgomeryValue01
