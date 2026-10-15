import ShielddSecurity.TransferScalarMontgomeryValue01
import ShielddSecurity.TransferScalarAdcShift01
import Init.Data.List.Nat.TakeDrop
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarPaddedCarry01
open TransferScalarFourRoundWrapper01 (modulusWords inverseWord nativeRound nativeRounds)
open TransferScalarCarrySchedule01 (macLoop)
open TransferScalarAdcShift01 (adc64)
open TransferScalarMaskedNormalization01 (sourceNormalize)
open TransferScalarLittleEndianBytes01 (wordsBytes decodeLE serializerBytes scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
/-! Source-shaped zero-padded scalar serializer reduction. Each round executes
the four low-limb MACs then the actual finite ADC on the next padded limb,
retains its low result and explicitly records its ignored outgoing carry.
Symbolic list induction derives fixed-width carry-wrapper equality and zero
for every ignored carry from the actual padded words, without a desired carry
premise. The exact four-round 32-byte canonical Montgomery result follows.
Pinned Rust constants/four-MAC/ADC/zero-high source shape is retained;
Rust primitive/trace/compiler/type/field bindings remain separate interfaces. -/

def paddedRound (words : List UInt64) : List UInt64 × UInt64 :=
  let low := words.take 4
  let mac := macLoop (low.headD 0 * inverseWord) 0 (low.zip modulusWords)
  let upper := adc64 ((words.drop 4).headD 0) 0 mac.2
  (mac.1.drop 1 ++ [upper.1] ++ words.drop 5, upper.2)

def paddedRounds : Nat → List UInt64 → List UInt64
  | 0, words => words
  | rounds + 1, words => paddedRounds rounds (paddedRound words).1

def paddedNoOverflow : Nat → List UInt64 → Prop
  | 0, _ => True
  | rounds + 1, words => (paddedRound words).2 = 0 ∧ paddedNoOverflow rounds (paddedRound words).1

theorem source_padded_round_is_exact_carry_wrapper_and_zero_ignored_carry
    (words tail : List UInt64) (four : words.length = 4) :
    paddedRound (words ++ 0 :: tail) = (nativeRound words ++ tail, 0) := by
  have taken : (words ++ 0 :: tail).take 4 = words := by
    rw [← four, List.take_append_length]
  have dropped : (words ++ 0 :: tail).drop 4 = 0 :: tail := by
    rw [← four, List.drop_append_length]
  have rest : (words ++ 0 :: tail).drop 5 = tail := by
    have width : 5 = words.length + 1 := by omega
    rw [width, List.drop_length_add_append]
    rfl
  unfold paddedRound
  rw [taken, dropped, rest, List.headD_cons]
  dsimp only
  rw [TransferScalarAdcShift01.zero_upper_limb_adc_retains_carry_without_overflow]
  rfl

theorem symbolic_zero_padded_walk_derives_fixed_wrapper_and_all_zero_ignored_carries
    (rounds : Nat) (words : List UInt64) (four : words.length = 4) :
    paddedRounds rounds (words ++ List.replicate rounds 0) = nativeRounds rounds words ∧
      paddedNoOverflow rounds (words ++ List.replicate rounds 0) := by
  induction rounds generalizing words with
  | zero => simp only [List.replicate_zero, List.append_nil, paddedRounds, nativeRounds, paddedNoOverflow, and_self]
  | succ rounds ih =>
    change paddedRounds rounds (paddedRound (words ++ List.replicate (rounds + 1) 0)).1 =
      nativeRounds rounds (nativeRound words) ∧
      (paddedRound (words ++ List.replicate (rounds + 1) 0)).2 = 0 ∧
      paddedNoOverflow rounds (paddedRound (words ++ List.replicate (rounds + 1) 0)).1
    rw [List.replicate_succ, source_padded_round_is_exact_carry_wrapper_and_zero_ignored_carry words _ four]
    have remaining := ih (nativeRound words)
      (TransferScalarFourRoundWrapper01.one_native_round_preserves_four_word_width words four)
    exact ⟨remaining.1, rfl, remaining.2⟩

theorem four_round_zero_padded_source_serializer_has_exact_width_and_montgomery_value
    (words : Vector UInt64 4) :
    (wordsBytes (sourceNormalize (paddedRounds 4 (words.toList ++ List.replicate 4 0)))).length = 32 ∧
      decodeLE (wordsBytes (sourceNormalize (paddedRounds 4 (words.toList ++ List.replicate 4 0)))) =
        montgomeryValue words ∧
      paddedNoOverflow 4 (words.toList ++ List.replicate 4 0) := by
  have reduced := symbolic_zero_padded_walk_derives_fixed_wrapper_and_all_zero_ignored_carries
    4 words.toList Vector.length_toList
  rw [reduced.1]
  exact ⟨TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width
      words.toList Vector.length_toList,
    TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value words,
    reduced.2⟩

set_option pp.all true in
#check @paddedRound
#print axioms paddedRound
set_option pp.all true in
#check @paddedRounds
#print axioms paddedRounds
set_option pp.all true in
#check @paddedNoOverflow
#print axioms paddedNoOverflow
set_option pp.all true in
#check @source_padded_round_is_exact_carry_wrapper_and_zero_ignored_carry
#print axioms source_padded_round_is_exact_carry_wrapper_and_zero_ignored_carry
set_option pp.all true in
#check @symbolic_zero_padded_walk_derives_fixed_wrapper_and_all_zero_ignored_carries
#print axioms symbolic_zero_padded_walk_derives_fixed_wrapper_and_all_zero_ignored_carries
set_option pp.all true in
#check @four_round_zero_padded_source_serializer_has_exact_width_and_montgomery_value
#print axioms four_round_zero_padded_source_serializer_has_exact_width_and_montgomery_value
end ShielddSecurity.TransferScalarPaddedCarry01
