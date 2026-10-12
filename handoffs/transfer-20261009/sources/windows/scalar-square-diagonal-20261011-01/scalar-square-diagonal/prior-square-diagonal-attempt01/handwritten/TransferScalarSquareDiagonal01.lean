import ShielddSecurity.TransferScalarSquareShift01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarSquareDiagonal01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords mac128 split128)
open TransferScalarAdcShift01 (adc64)
open TransferScalarSquareCross01 (crossValue)
/-! The four square diagonal terms use one MAC and one ADC per pair.
The symbolic pair recurrence retains its final carry and derives the full
integer before any carry is discarded. Algebraically adding these diagonal
terms to the doubled cross terms reconstructs the exact square. -/

def diagonalValue : List UInt64 → Nat
  | [] => 0
  | word :: rest => word.toNat * word.toNat + radix64 ^ 2 * diagonalValue rest

def diagonalWalk : List UInt64 → UInt64 → List UInt64 → List UInt64 × UInt64
  | [], carry, _ => ([], carry)
  | word :: rest, carry, low :: high :: accumulated =>
    let first := split128 (mac128 low word word carry)
    let second := adc64 0 high first.2
    let tail := diagonalWalk rest second.2 accumulated
    (first.1 :: second.1 :: tail.1, tail.2)
  | _ :: rest, carry, _ => diagonalWalk rest carry []

theorem symbolic_diagonal_and_cross_values_reconstruct_exact_square (words : List UInt64) :
    packWords words * packWords words = diagonalValue words + 2 * radix64 * crossValue words := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    change (word.toNat + radix64 * packWords rest) * (word.toNat + radix64 * packWords rest) =
      (word.toNat * word.toNat + radix64 ^ 2 * diagonalValue rest) +
        2 * radix64 * (word.toNat * packWords rest + radix64 ^ 2 * crossValue rest)
    calc
      _ = word.toNat * word.toNat + 2 * radix64 * (word.toNat * packWords rest) +
          radix64 ^ 2 * (packWords rest * packWords rest) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.pow_two]
        change _ = _ + (1 + 1) * radix64 * (word.toNat * packWords rest) + _
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_add]
        ac_rfl
      _ = _ := by
        rw [ih, Nat.mul_add, Nat.mul_add]
        ac_rfl

theorem symbolic_diagonal_mac_adc_walk_derives_width_and_full_integer
    (words : List UInt64) (carry : UInt64) (accumulated : List UInt64)
    (width : accumulated.length = 2 * words.length) :
    (diagonalWalk words carry accumulated).1.length = 2 * words.length ∧
      packWords (diagonalWalk words carry accumulated).1 +
        radix64 ^ (2 * words.length) * (diagonalWalk words carry accumulated).2.toNat =
          packWords accumulated + diagonalValue words + carry.toNat := by
  induction words generalizing carry accumulated with
  | nil =>
    have empty : accumulated = [] := List.eq_nil_of_length_eq_zero width
    subst accumulated
    constructor
    · rfl
    · change 0 + radix64 ^ (2 * 0) * carry.toNat = 0 + 0 + carry.toNat
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | cons word rest ih =>
    cases accumulated with
    | nil => simp only [List.length_nil, List.length_cons] at width; omega
    | cons low remaining =>
      cases remaining with
      | nil => simp only [List.length_nil, List.length_cons] at width; omega
      | cons high accumulated =>
        have tailWidth : accumulated.length = 2 * rest.length := by
          simp only [List.length_cons] at width
          omega
        let first := split128 (mac128 low word word carry)
        let second := adc64 0 high first.2
        let tail := diagonalWalk rest second.2 accumulated
        have tailContract := ih second.2 accumulated tailWidth
        have firstValue := TransferScalarWordPrimitives01.widened_u64_mac_low_word_and_carry_conserve_value low word word carry
        have secondValue := TransferScalarAdcShift01.widened_adc_low_word_and_carry_conserve_sum 0 high first.2
        change first.1.toNat + radix64 * first.2.toNat = low.toNat + word.toNat * word.toNat + carry.toNat at firstValue
        change second.1.toNat + radix64 * second.2.toNat = high.toNat + first.2.toNat at secondValue
        change tail.1.length = 2 * rest.length ∧
          packWords tail.1 + radix64 ^ (2 * rest.length) * tail.2.toNat =
            packWords accumulated + diagonalValue rest + second.2.toNat at tailContract
        change (first.1 :: second.1 :: tail.1).length = 2 * (rest.length + 1) ∧
          packWords (first.1 :: second.1 :: tail.1) + radix64 ^ (2 * (rest.length + 1)) * tail.2.toNat =
            packWords (low :: high :: accumulated) +
              (word.toNat * word.toNat + radix64 ^ 2 * diagonalValue rest) + carry.toNat
        constructor
        · simp only [List.length_cons, tailContract.1]
          omega
        · have power : radix64 ^ (2 * (rest.length + 1)) = radix64 ^ 2 * radix64 ^ (2 * rest.length) := by
            rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (2 * rest.length) 2, Nat.pow_add]
          calc
            _ = first.1.toNat + radix64 * second.1.toNat +
                radix64 ^ 2 * (packWords tail.1 + radix64 ^ (2 * rest.length) * tail.2.toNat) := by
              rw [packWords, packWords, power, Nat.mul_add, Nat.mul_add, Nat.pow_two]
              ac_rfl
            _ = first.1.toNat + radix64 * second.1.toNat +
                radix64 ^ 2 * (packWords accumulated + diagonalValue rest + second.2.toNat) := by rw [tailContract.2]
            _ = (first.1.toNat + radix64 * (second.1.toNat + radix64 * second.2.toNat)) +
                radix64 ^ 2 * (packWords accumulated + diagonalValue rest) := by
              rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.pow_two]
              ac_rfl
            _ = (first.1.toNat + radix64 * (high.toNat + first.2.toNat)) +
                radix64 ^ 2 * (packWords accumulated + diagonalValue rest) := by rw [secondValue]
            _ = (first.1.toNat + radix64 * first.2.toNat) + radix64 * high.toNat +
                radix64 ^ 2 * (packWords accumulated + diagonalValue rest) := by rw [Nat.mul_add]; ac_rfl
            _ = (low.toNat + word.toNat * word.toNat + carry.toNat) + radix64 * high.toNat +
                radix64 ^ 2 * (packWords accumulated + diagonalValue rest) := by rw [firstValue]
            _ = _ := by
              rw [packWords, packWords, Nat.mul_add, Nat.mul_add, Nat.pow_two]
              ac_rfl

set_option pp.all true in
#check @diagonalValue
#print axioms diagonalValue
set_option pp.all true in
#check @diagonalWalk
#print axioms diagonalWalk
set_option pp.all true in
#check @symbolic_diagonal_and_cross_values_reconstruct_exact_square
#print axioms symbolic_diagonal_and_cross_values_reconstruct_exact_square
set_option pp.all true in
#check @symbolic_diagonal_mac_adc_walk_derives_width_and_full_integer
#print axioms symbolic_diagonal_mac_adc_walk_derives_width_and_full_integer
end ShielddSecurity.TransferScalarSquareDiagonal01
