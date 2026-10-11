import ShielddSecurity.TransferScalarWideRound01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarWideWalk01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarFourRoundWrapper01 (inverseWord)
open TransferScalarWideRound01 (wideValue wideRoundParts)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Symbolic source-shaped wide Montgomery round walk. The current input
words and deferred ADC carry determine every next state; no desired result
or cancellation is supplied. Width, modular relation and final <2p bound
derive by induction using small exact row lemmas. Native source execution,
primitive/compiler correspondence and final ignored carry remain separate. -/

def wideRound (state : List UInt64 × UInt64) : List UInt64 × UInt64 :=
  wideRoundParts (state.1.take 4) (state.1.drop 4 |>.headD 0) (state.1.drop 5) state.2

def wideRounds : Nat → (List UInt64 × UInt64) → (List UInt64 × UInt64)
  | 0, state => state
  | rounds + 1, state => wideRounds rounds (wideRound state)

theorem finite_words_split_at_actual_upper_limb (words : List UInt64) (enough : 5 ≤ words.length) :
    words = words.take 4 ++ (words.drop 4 |>.headD 0) :: words.drop 5 := by
  have split := List.take_append_drop 4 words
  have droppedWidth : (words.drop 4).length = words.length - 4 := List.length_drop
  cases dropped : words.drop 4 with
  | nil => rw [dropped, List.length_nil] at droppedWidth; omega
  | cons upper tail =>
    rw [dropped] at split
    have nested : (words.drop 4).drop 1 = words.drop 5 := List.drop_drop
    rw [dropped] at nested
    have tailEqual : words.drop 5 = tail := nested.symm
    rw [tailEqual]
    exact split.symm

theorem wide_round_derives_width_and_exact_integer_equation
    (state : List UInt64 × UInt64) (enough : 5 ≤ state.1.length) :
    (wideRound state).1.length = state.1.length - 1 ∧
      radix64 * wideValue (wideRound state) = wideValue state +
        ((state.1.take 4).headD 0 * inverseWord).toNat * nullifierModulus := by
  have four : (state.1.take 4).length = 4 := List.length_take_of_le (by omega)
  have split := finite_words_split_at_actual_upper_limb state.1 enough
  constructor
  · have width := TransferScalarWideRound01.wide_round_preserves_remaining_word_count
      (state.1.take 4) (state.1.drop 4 |>.headD 0) state.2 (state.1.drop 5) four
    change (wideRoundParts (state.1.take 4) (state.1.drop 4 |>.headD 0) (state.1.drop 5) state.2).1.length = _
    rw [width, List.length_drop]
    omega
  · have row := TransferScalarWideRound01.wide_round_derives_exact_integer_equation_with_deferred_carry
      (state.1.take 4) (state.1.drop 4 |>.headD 0) state.2 (state.1.drop 5) four
    rw [← split] at row
    exact row

theorem symbolic_wide_walk_derives_final_width_and_modular_value
    (rounds : Nat) (state : List UInt64 × UInt64) (width : state.1.length = 4 + rounds) :
    (wideRounds rounds state).1.length = 4 ∧
      (radix64 ^ rounds * wideValue (wideRounds rounds state)) % nullifierModulus =
        wideValue state % nullifierModulus := by
  induction rounds generalizing state with
  | zero => exact ⟨width, by simp only [wideRounds, Nat.pow_zero, Nat.one_mul]⟩
  | succ rounds ih =>
    have step := wide_round_derives_width_and_exact_integer_equation state (by omega)
    have nextWidth : (wideRound state).1.length = 4 + rounds := by rw [step.1, width]; omega
    have tail := ih (wideRound state) nextWidth
    constructor
    · exact tail.1
    · change (radix64 ^ (rounds + 1) * wideValue (wideRounds rounds (wideRound state))) % nullifierModulus = _
      have reassoc : radix64 ^ (rounds + 1) * wideValue (wideRounds rounds (wideRound state)) =
          radix64 * (radix64 ^ rounds * wideValue (wideRounds rounds (wideRound state))) := by
        rw [Nat.pow_succ]; ac_rfl
      rw [reassoc, Nat.mul_mod, tail.2, ← Nat.mul_mod, step.2, Nat.add_mul_mod_self_right]

theorem finite_multiplier_round_reduces_symbolic_range
    (rounds current next : Nat) (multiplier : UInt64)
    (equation : radix64 * next = current + multiplier.toNat * nullifierModulus)
    (bound : current < nullifierModulus * (radix64 ^ (rounds + 1) + 1)) :
    next < nullifierModulus * (radix64 ^ rounds + 1) := by
  have multiplierBound : multiplier.toNat < radix64 := multiplier.toNat_lt
  have limited : multiplier.toNat + 1 ≤ radix64 := by omega
  have increased := Nat.add_lt_add_right bound (multiplier.toNat * nullifierModulus)
  have scaled : radix64 * next < radix64 * (nullifierModulus * (radix64 ^ rounds + 1)) := by
    rw [equation]
    calc
      _ < nullifierModulus * (radix64 ^ (rounds + 1) + 1) + multiplier.toNat * nullifierModulus := increased
      _ = nullifierModulus * radix64 ^ (rounds + 1) + nullifierModulus * (multiplier.toNat + 1) := by
        simp only [Nat.mul_add, Nat.mul_one]; ac_rfl
      _ ≤ nullifierModulus * radix64 ^ (rounds + 1) + nullifierModulus * radix64 :=
        Nat.add_le_add_left (Nat.mul_le_mul_left nullifierModulus limited) _
      _ = _ := by simp only [Nat.pow_succ, Nat.mul_add, Nat.mul_one]; ac_rfl
  exact Nat.lt_of_mul_lt_mul_left scaled

theorem symbolic_wide_walk_derives_final_value_below_twice_modulus
    (rounds : Nat) (state : List UInt64 × UInt64) (width : state.1.length = 4 + rounds)
    (bound : wideValue state < nullifierModulus * (radix64 ^ rounds + 1)) :
    wideValue (wideRounds rounds state) < 2 * nullifierModulus := by
  induction rounds generalizing state with
  | zero => simpa only [wideRounds, Nat.pow_zero, Nat.mul_comm] using bound
  | succ rounds ih =>
    have step := wide_round_derives_width_and_exact_integer_equation state (by omega)
    have nextWidth : (wideRound state).1.length = 4 + rounds := by rw [step.1, width]; omega
    have nextBound := finite_multiplier_round_reduces_symbolic_range rounds (wideValue state)
      (wideValue (wideRound state)) ((state.1.take 4).headD 0 * inverseWord) step.2 bound
    exact ih (wideRound state) nextWidth nextBound

set_option pp.all true in
#check @wideRound
#print axioms wideRound
set_option pp.all true in
#check @wideRounds
#print axioms wideRounds
set_option pp.all true in
#check @finite_words_split_at_actual_upper_limb
#print axioms finite_words_split_at_actual_upper_limb
set_option pp.all true in
#check @wide_round_derives_width_and_exact_integer_equation
#print axioms wide_round_derives_width_and_exact_integer_equation
set_option pp.all true in
#check @symbolic_wide_walk_derives_final_width_and_modular_value
#print axioms symbolic_wide_walk_derives_final_width_and_modular_value
set_option pp.all true in
#check @finite_multiplier_round_reduces_symbolic_range
#print axioms finite_multiplier_round_reduces_symbolic_range
set_option pp.all true in
#check @symbolic_wide_walk_derives_final_value_below_twice_modulus
#print axioms symbolic_wide_walk_derives_final_value_below_twice_modulus
end ShielddSecurity.TransferScalarWideWalk01
