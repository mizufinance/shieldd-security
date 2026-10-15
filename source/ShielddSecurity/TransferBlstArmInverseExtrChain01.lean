import ShielddSecurity.TransferBlstArmInverseExtrWord01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseExtrChain01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseExtrWord01 (sourceExtractWord)
attribute [local irreducible] sourceExtractWord

/-! Symbolic adjacent-word EXTR chain. The unconsumed final high word is
retained explicitly, yielding a complete quotient equation before taking
the low output-width residue. No native instruction execution is inferred. -/

def sourceExtractChain (shift : Nat) : List UInt64 → List UInt64 × UInt64
  | [] => ([], 0)
  | [top] => ([], top)
  | low :: high :: rest =>
      let after := sourceExtractChain shift (high :: rest)
      (sourceExtractWord high low shift :: after.1, after.2)

theorem every_original_adjacent_extraction_chain_retains_exactly_the_lower_word_count
    (shift : Nat) (words : List UInt64) :
    (sourceExtractChain shift words).1.length = words.length - 1 := by
  induction words with
  | nil => rfl
  | cons low rest ih =>
    cases rest with
    | nil => rfl
    | cons high tail =>
      change (sourceExtractChain shift (high :: tail)).1.length + 1 = (tail.length + 1 + 1) - 1
      rw [ih]
      simp only [List.length_cons]
      omega

theorem an_original_adjacent_extraction_and_the_remaining_quotient_conserve_the_entire_input_quotient
    (low high : UInt64) (rest : List UInt64) (shift : Nat) (positive : 0 < shift) (bounded : shift < 64) :
    (sourceExtractWord high low shift).toNat + radix64 * (packWords (high :: rest) / 2 ^ shift) =
      packWords (low :: high :: rest) / 2 ^ shift := by
  let scale := 2 ^ (64 - shift)
  let divisor := 2 ^ shift
  have divisorPositive : 0 < divisor := Nat.two_pow_pos shift
  have factorization : radix64 = scale * divisor := by
    dsimp only [scale, divisor, radix64]
    rw [←Nat.pow_add, show (64 - shift) + shift = 64 by omega]
  have whole : packWords (low :: high :: rest) / divisor = scale * packWords (high :: rest) + low.toNat / divisor := by
    change (low.toNat + radix64 * packWords (high :: rest)) / divisor = _
    rw [Nat.add_comm low.toNat]
    exact TransferBlstArmInverseWindowArithmetic01.symbolic_two_limb_window_division_is_exact_without_a_tail_premise
      radix64 scale divisor (packWords (high :: rest)) low.toNat divisorPositive factorization
  have remaining : packWords (high :: rest) / divisor = scale * packWords rest + high.toNat / divisor := by
    change (high.toNat + radix64 * packWords rest) / divisor = _
    rw [Nat.add_comm high.toNat]
    exact TransferBlstArmInverseWindowArithmetic01.symbolic_two_limb_window_division_is_exact_without_a_tail_premise
      radix64 scale divisor (packWords rest) high.toNat divisorPositive factorization
  have extracted := TransferBlstArmInverseExtrWord01.original_extr_word_derives_both_entire_nonoverlapping_window_fragments high low shift positive bounded
  change (sourceExtractWord high low shift).toNat = scale * (high.toNat % divisor) + low.toNat / divisor at extracted
  change (sourceExtractWord high low shift).toNat + radix64 * (packWords (high :: rest) / divisor) =
    packWords (low :: high :: rest) / divisor
  rw [whole, remaining, extracted]
  change (scale * (high.toNat % divisor) + low.toNat / divisor) + radix64 * (scale * packWords rest + high.toNat / divisor) =
    scale * (high.toNat + radix64 * packWords rest) + low.toNat / divisor
  have highSplit := Nat.mod_add_div high.toNat divisor
  have lifted := congrArg (fun value : Nat => scale * value) highSplit
  dsimp only at lifted
  calc
    _ = scale * (high.toNat % divisor + divisor * (high.toNat / divisor)) +
        scale * radix64 * packWords rest + low.toNat / divisor := by rw [factorization]; ring1
    _ = scale * high.toNat + scale * radix64 * packWords rest + low.toNat / divisor := by rw [lifted]
    _ = _ := by ring1

theorem a_symbolic_radix_lift_composes_one_extracted_word_with_the_remaining_quotient
    (radix count head output top tailQuotient inputQuotient : Nat)
    (remaining : output + radix ^ count * top = tailQuotient)
    (step : head + radix * tailQuotient = inputQuotient) :
    head + radix * output + radix ^ (count + 1) * top = inputQuotient := by
  calc
    _ = head + radix * (output + radix ^ count * top) := by rw [Nat.pow_succ]; ring1
    _ = head + radix * tailQuotient := by rw [remaining]
    _ = _ := step

theorem the_entire_original_extraction_chain_and_retained_high_word_conserve_the_full_input_quotient
    (shift : Nat) (words : List UInt64) (positive : 0 < shift) (bounded : shift < 64) :
    packWords (sourceExtractChain shift words).1 +
      radix64 ^ (words.length - 1) * ((sourceExtractChain shift words).2.toNat / 2 ^ shift) =
        packWords words / 2 ^ shift := by
  induction words with
  | nil => simp [sourceExtractChain, packWords]
  | cons low rest ih =>
    cases rest with
    | nil => simp [sourceExtractChain, packWords]
    | cons high tail =>
      have previous := ih
      change packWords (sourceExtractChain shift (high :: tail)).1 +
          radix64 ^ tail.length * ((sourceExtractChain shift (high :: tail)).2.toNat / 2 ^ shift) =
            packWords (high :: tail) / 2 ^ shift at previous
      change (sourceExtractWord high low shift).toNat + radix64 * packWords (sourceExtractChain shift (high :: tail)).1 +
          radix64 ^ (tail.length + 1) * ((sourceExtractChain shift (high :: tail)).2.toNat / 2 ^ shift) =
            packWords (low :: high :: tail) / 2 ^ shift
      exact a_symbolic_radix_lift_composes_one_extracted_word_with_the_remaining_quotient
        radix64 tail.length (sourceExtractWord high low shift).toNat (packWords (sourceExtractChain shift (high :: tail)).1)
        ((sourceExtractChain shift (high :: tail)).2.toNat / 2 ^ shift)
        (packWords (high :: tail) / 2 ^ shift) (packWords (low :: high :: tail) / 2 ^ shift)
        previous (an_original_adjacent_extraction_and_the_remaining_quotient_conserve_the_entire_input_quotient low high tail shift positive bounded)

attribute [local irreducible] sourceExtractChain

theorem the_entire_original_extraction_chain_has_the_exact_low_word_quotient_residue
    (shift : Nat) (words : List UInt64) (positive : 0 < shift) (bounded : shift < 64) :
    packWords (sourceExtractChain shift words).1 = (packWords words / 2 ^ shift) % (radix64 ^ (words.length - 1)) := by
  have entire := the_entire_original_extraction_chain_and_retained_high_word_conserve_the_full_input_quotient shift words positive bounded
  have outputBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (sourceExtractChain shift words).1
  rw [every_original_adjacent_extraction_chain_retains_exactly_the_lower_word_count] at outputBound
  have reduced := congrArg (fun value : Nat => value % (radix64 ^ (words.length - 1))) entire
  dsimp only at reduced
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt outputBound] at reduced
  exact reduced

set_option pp.all true in
#check @sourceExtractChain
#print axioms sourceExtractChain
set_option pp.all true in
#check @every_original_adjacent_extraction_chain_retains_exactly_the_lower_word_count
#print axioms every_original_adjacent_extraction_chain_retains_exactly_the_lower_word_count
set_option pp.all true in
#check @an_original_adjacent_extraction_and_the_remaining_quotient_conserve_the_entire_input_quotient
#print axioms an_original_adjacent_extraction_and_the_remaining_quotient_conserve_the_entire_input_quotient
set_option pp.all true in
#check @a_symbolic_radix_lift_composes_one_extracted_word_with_the_remaining_quotient
#print axioms a_symbolic_radix_lift_composes_one_extracted_word_with_the_remaining_quotient
set_option pp.all true in
#check @the_entire_original_extraction_chain_and_retained_high_word_conserve_the_full_input_quotient
#print axioms the_entire_original_extraction_chain_and_retained_high_word_conserve_the_full_input_quotient
set_option pp.all true in
#check @the_entire_original_extraction_chain_has_the_exact_low_word_quotient_residue
#print axioms the_entire_original_extraction_chain_has_the_exact_low_word_quotient_residue
end ShielddSecurity.TransferBlstArmInverseExtrChain01
