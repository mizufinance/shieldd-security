import ShielddSecurity.TransferScalarWideProduct01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarWideRound01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarCarrySchedule01 (macLoop dropLowAndAppendCarry)
open TransferScalarFourRoundWrapper01 (modulusWords inverseWord)
open TransferScalarAdcShift01 (adc64)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! One wide Montgomery source round. Four low words use the proved MAC
schedule; the next upper word consumes both the previous deferred ADC carry
and the MAC carry. The new deferred carry has weight B^4 after shifting.
Low-word cancellation and exact full integer conservation are conclusions.
Native compiler/primitive/full trace binding and four-round reduction remain
separate. No caller-provided cancellation or desired output assumption. -/

def wideValue (state : List UInt64 × UInt64) : Nat :=
  packWords state.1 + radix64 ^ 4 * state.2.toNat

def wideRoundParts (low : List UInt64) (upper : UInt64) (tail : List UInt64)
    (pending : UInt64) : List UInt64 × UInt64 :=
  let output := macLoop (low.headD 0 * inverseWord) 0 (low.zip modulusWords)
  let shifted := adc64 upper pending output.2
  (output.1.drop 1 ++ shifted.1 :: tail, shifted.2)

theorem actual_mac_low_word_is_zero (low : List UInt64) (four : low.length = 4) :
    ((macLoop (low.headD 0 * inverseWord) 0 (low.zip modulusWords)).1.headD 0).toNat = 0 := by
  have row := TransferScalarWideProduct01.finite_mac_row_derives_exact_accumulation_equation
    (low.headD 0 * inverseWord) modulusWords low (by decide) four
  rw [TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus] at row
  have modulo := congrArg (fun value => value % radix64) row
  rw [Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt ((macLoop (low.headD 0 * inverseWord) 0 (low.zip modulusWords)).1.headD 0).toNat_lt,
    TransferScalarMontgomeryValue01.derived_round_numerator_is_divisible_by_radix] at modulo
  exact modulo

theorem four_low_words_and_mac_carry_have_exact_shifted_equation
    (low : List UInt64) (four : low.length = 4) :
    radix64 * packWords (dropLowAndAppendCarry (macLoop (low.headD 0 * inverseWord) 0 (low.zip modulusWords))) =
      packWords low + (low.headD 0 * inverseWord).toNat * nullifierModulus := by
  have row := TransferScalarWideProduct01.finite_mac_row_derives_exact_accumulation_equation
    (low.headD 0 * inverseWord) modulusWords low (by decide) four
  rw [TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus,
    actual_mac_low_word_is_zero low four, Nat.zero_add] at row
  exact row

theorem wide_round_preserves_remaining_word_count
    (low : List UInt64) (upper pending : UInt64) (tail : List UInt64) (four : low.length = 4) :
    (wideRoundParts low upper tail pending).1.length = 4 + tail.length := by
  have width := TransferScalarCarrySchedule01.carry_walk_retains_limb_count
    (low.headD 0 * inverseWord) 0 (low.zip modulusWords)
  rw [List.length_zip, four] at width
  have modulusWidth : modulusWords.length = 4 := by decide
  rw [modulusWidth, Nat.min_self] at width
  unfold wideRoundParts
  rw [List.length_append, List.length_drop, width, List.length_cons]
  omega

theorem wide_round_derives_exact_integer_equation_with_deferred_carry
    (low : List UInt64) (upper pending : UInt64) (tail : List UInt64) (four : low.length = 4) :
    radix64 * wideValue (wideRoundParts low upper tail pending) =
      packWords (low ++ upper :: tail) + radix64 ^ 4 * pending.toNat +
        (low.headD 0 * inverseWord).toNat * nullifierModulus := by
  let output := macLoop (low.headD 0 * inverseWord) 0 (low.zip modulusWords)
  let shifted := adc64 upper pending output.2
  have width : output.1.length = 4 := by
    have original := TransferScalarCarrySchedule01.carry_walk_retains_limb_count
      (low.headD 0 * inverseWord) 0 (low.zip modulusWords)
    simpa only [List.length_zip, four, show modulusWords.length = 4 from by decide, Nat.min_self] using original
  have dropped : (output.1.drop 1).length = 3 := by rw [List.length_drop, width]
  have row := four_low_words_and_mac_carry_have_exact_shifted_equation low four
  change radix64 * packWords (output.1.drop 1 ++ [output.2]) = _ at row
  rw [TransferScalarCarrySchedule01.packing_append_preserves_positional_value, dropped] at row
  change radix64 * (packWords (output.1.drop 1) + radix64 ^ 3 * output.2.toNat) = _ at row
  have carry := TransferScalarAdcShift01.widened_adc_low_word_and_carry_conserve_sum upper pending output.2
  change shifted.1.toNat + radix64 * shifted.2.toNat = upper.toNat + pending.toNat + output.2.toNat at carry
  change radix64 * (packWords (output.1.drop 1 ++ shifted.1 :: tail) + radix64 ^ 4 * shifted.2.toNat) = _
  rw [TransferScalarCarrySchedule01.packing_append_preserves_positional_value, dropped,
    TransferScalarCarrySchedule01.packing_append_preserves_positional_value low (upper :: tail), four]
  change radix64 * (packWords (output.1.drop 1) + radix64 ^ 3 * (shifted.1.toNat + radix64 * packWords tail) +
    radix64 ^ 4 * shifted.2.toNat) =
    packWords low + radix64 ^ 4 * (upper.toNat + radix64 * packWords tail) +
    radix64 ^ 4 * pending.toNat + (low.headD 0 * inverseWord).toNat * nullifierModulus
  calc
    _ = radix64 * packWords (output.1.drop 1) + radix64 ^ 4 *
        (shifted.1.toNat + radix64 * shifted.2.toNat) + radix64 ^ 5 * packWords tail := by
      simp only [Nat.pow_succ, Nat.mul_add, Nat.add_mul]; ac_rfl
    _ = radix64 * packWords (output.1.drop 1) + radix64 ^ 4 *
        (upper.toNat + pending.toNat + output.2.toNat) + radix64 ^ 5 * packWords tail := by rw [carry]
    _ = radix64 * (packWords (output.1.drop 1) + radix64 ^ 3 * output.2.toNat) +
        radix64 ^ 4 * (upper.toNat + pending.toNat) + radix64 ^ 5 * packWords tail := by
      simp only [Nat.pow_succ, Nat.mul_add, Nat.add_mul]; ac_rfl
    _ = _ := by rw [row]; simp only [Nat.pow_succ, Nat.mul_add, Nat.add_mul]; ac_rfl

end ShielddSecurity.TransferScalarWideRound01
