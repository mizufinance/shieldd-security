import ShielddSecurity.TransferBlstArmInverseCarrySplit01
import ShielddSecurity.TransferBlstArmInverseWordMultiplyCarry01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePartialProductSplit01
open TransferBlstArmCarryChains01 (sourceAddCarry sourceAddCarryChain)
open TransferBlstArmInverseWordMultiply01 (sourceMultiplyWordLow sourceMultiplyWordHigh)
open TransferBlstArmInverseWordMultiplyCarry01 (sourceUnsignedWordMultiply)
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
attribute [local irreducible] sourceAddCarry sourceAddCarryChain sourceMultiplyWordLow sourceMultiplyWordHigh sourceUnsignedWordMultiply

/-! Source MUL/UMULH shifted partial products can stop at any symbolic
limb boundary and resume using both the actual previous high product and
the actual captured addition carry. The original full unsigned product is
recovered by one final ADC. No compressed signed operand or ISA claim. -/

def sourcePartialProductPairs (multiplier : UInt64) : UInt64 → List UInt64 → List (UInt64 × UInt64) × UInt64
  | previousHigh, [] => ([], previousHigh)
  | previousHigh, word :: rest =>
      let after := sourcePartialProductPairs multiplier (sourceMultiplyWordHigh word multiplier) rest
      ((sourceMultiplyWordLow word multiplier, previousHigh) :: after.1, after.2)

theorem every_partial_product_pair_list_plus_its_final_high_word_is_the_entire_original_shifted_list
    (words : List UInt64) (multiplier previousHigh : UInt64) :
    let pairs := sourcePartialProductPairs multiplier previousHigh words
    pairs.1 ++ [(0, pairs.2)] =
      ((words.map (fun word => sourceMultiplyWordLow word multiplier)) ++ [0]).zip
        (previousHigh :: words.map (fun word => sourceMultiplyWordHigh word multiplier)) := by
  induction words generalizing previousHigh with
  | nil => rfl
  | cons word rest ih =>
    simp only [sourcePartialProductPairs, List.cons_append, List.map_cons, List.zip_cons_cons, ih]

theorem every_partial_product_pair_producer_can_pause_and_resume_with_its_actual_high_product
    (low high : List UInt64) (multiplier previousHigh : UInt64) :
    sourcePartialProductPairs multiplier previousHigh (low ++ high) =
      let first := sourcePartialProductPairs multiplier previousHigh low
      let last := sourcePartialProductPairs multiplier first.2 high
      (first.1 ++ last.1, last.2) := by
  induction low generalizing previousHigh with
  | nil => simp only [List.nil_append, sourcePartialProductPairs]
  | cons word rest ih =>
    simp only [List.cons_append, sourcePartialProductPairs, ih]

attribute [local irreducible] sourcePartialProductPairs

def sourcePartialWordMultiply (words : List UInt64) (multiplier previousHigh : UInt64)
    (carry : Bool) : List UInt64 × Bool × UInt64 :=
  let pairs := sourcePartialProductPairs multiplier previousHigh words
  let output := sourceAddCarryChain carry pairs.1
  (output.1, output.2, pairs.2)

theorem every_partial_word_product_can_resume_with_both_its_actual_high_word_and_captured_carry
    (low high : List UInt64) (multiplier previousHigh : UInt64) (carry : Bool) :
    sourcePartialWordMultiply (low ++ high) multiplier previousHigh carry =
      let first := sourcePartialWordMultiply low multiplier previousHigh carry
      let last := sourcePartialWordMultiply high multiplier first.2.2 first.2.1
      (first.1 ++ last.1, last.2.1, last.2.2) := by
  simp only [sourcePartialWordMultiply,
    every_partial_product_pair_producer_can_pause_and_resume_with_its_actual_high_product,
    TransferBlstArmInverseCarrySplit01.every_symbolic_source_carry_chain_can_pause_and_resume_with_its_actual_flag]

attribute [local irreducible] sourcePartialWordMultiply

theorem the_original_entire_unsigned_product_is_the_partial_product_followed_by_its_actual_final_adc
    (words : List UInt64) (multiplier : UInt64) :
    sourceUnsignedWordMultiply words multiplier =
      let first := sourcePartialWordMultiply words multiplier 0 false
      let last := sourceAddCarry 0 first.2.2 first.2.1
      (first.1 ++ [last.1], last.2) := by
  unfold sourceUnsignedWordMultiply
  rw [← every_partial_product_pair_list_plus_its_final_high_word_is_the_entire_original_shifted_list,
    TransferBlstArmInverseCarrySplit01.every_symbolic_source_carry_chain_can_pause_and_resume_with_its_actual_flag]
  unfold sourcePartialWordMultiply
  simp only [sourceAddCarryChain]

theorem one_source_partial_product_word_consumes_the_actual_previous_high_and_carry
    (word : UInt64) (rest : List UInt64) (multiplier previousHigh : UInt64) (carry : Bool) :
    sourcePartialWordMultiply (word :: rest) multiplier previousHigh carry =
      let step := sourceAddCarry (sourceMultiplyWordLow word multiplier) previousHigh carry
      let after := sourcePartialWordMultiply rest multiplier (sourceMultiplyWordHigh word multiplier) step.2
      (step.1 :: after.1, after.2.1, after.2.2) := by
  unfold sourcePartialWordMultiply
  simp only [sourcePartialProductPairs, sourceAddCarryChain]

theorem every_symbolic_partial_product_pair_list_retains_the_entire_input_word_count
    (words : List UInt64) (multiplier previousHigh : UInt64) :
    (sourcePartialProductPairs multiplier previousHigh words).1.length = words.length := by
  induction words generalizing previousHigh with
  | nil => simp only [sourcePartialProductPairs, List.length_nil]
  | cons word rest ih =>
    simp only [sourcePartialProductPairs, List.length_cons, ih]

theorem every_partial_word_product_retains_the_entire_input_word_count
    (words : List UInt64) (multiplier previousHigh : UInt64) (carry : Bool) :
    (sourcePartialWordMultiply words multiplier previousHigh carry).1.length = words.length := by
  unfold sourcePartialWordMultiply
  rw [TransferBlstArmCarryChains01.actual_add_chain_retains_the_source_limb_count,
    every_symbolic_partial_product_pair_list_retains_the_entire_input_word_count]

theorem every_partial_word_product_conserves_the_full_integer_with_both_captured_boundary_values
    (words : List UInt64) (multiplier previousHigh : UInt64) (carry : Bool) :
    let output := sourcePartialWordMultiply words multiplier previousHigh carry
    packWords output.1 + radix64 ^ words.length * (output.2.2.toNat + output.2.1.toNat) =
      packWords words * multiplier.toNat + previousHigh.toNat + carry.toNat := by
  induction words generalizing previousHigh carry with
  | nil =>
    simp only [sourcePartialWordMultiply, sourcePartialProductPairs, sourceAddCarryChain,
      packWords, List.length_nil, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.zero_mul]
  | cons word rest ih =>
    let step := sourceAddCarry (sourceMultiplyWordLow word multiplier) previousHigh carry
    let after := sourcePartialWordMultiply rest multiplier (sourceMultiplyWordHigh word multiplier) step.2
    have tail := ih (sourceMultiplyWordHigh word multiplier) step.2
    have head := TransferBlstArmCarryChains01.actual_add_carry_arithmetic_conserves_the_full_integer
      (sourceMultiplyWordLow word multiplier) previousHigh carry
    have product := TransferBlstArmInverseWordMultiply01.original_low_and_high_word_products_conserve_the_entire_unsigned_product word multiplier
    rw [one_source_partial_product_word_consumes_the_actual_previous_high_and_carry]
    change step.1.toNat + radix64 * packWords after.1 +
        radix64 ^ (rest.length + 1) * (after.2.2.toNat + after.2.1.toNat) =
      (word.toNat + radix64 * packWords rest) * multiplier.toNat + previousHigh.toNat + carry.toNat
    calc
      _ = step.1.toNat + radix64 * (packWords after.1 +
          radix64 ^ rest.length * (after.2.2.toNat + after.2.1.toNat)) := by
        rw [Nat.pow_succ]
        ring1
      _ = step.1.toNat + radix64 * (packWords rest * multiplier.toNat +
          (sourceMultiplyWordHigh word multiplier).toNat + step.2.toNat) := by rw [tail]
      _ = (step.1.toNat + radix64 * step.2.toNat) +
          radix64 * (sourceMultiplyWordHigh word multiplier).toNat +
          radix64 * packWords rest * multiplier.toNat := by ring1
      _ = ((sourceMultiplyWordLow word multiplier).toNat + previousHigh.toNat + carry.toNat) +
          radix64 * (sourceMultiplyWordHigh word multiplier).toNat +
          radix64 * packWords rest * multiplier.toNat := by rw [head]
      _ = ((sourceMultiplyWordLow word multiplier).toNat +
          radix64 * (sourceMultiplyWordHigh word multiplier).toNat) +
          radix64 * packWords rest * multiplier.toNat + previousHigh.toNat + carry.toNat := by ring1
      _ = word.toNat * multiplier.toNat + radix64 * packWords rest * multiplier.toNat +
          previousHigh.toNat + carry.toNat := by rw [product]
      _ = _ := by ring1

set_option pp.all true in
#check @sourcePartialProductPairs
#print axioms sourcePartialProductPairs
set_option pp.all true in
#check @every_partial_product_pair_list_plus_its_final_high_word_is_the_entire_original_shifted_list
#print axioms every_partial_product_pair_list_plus_its_final_high_word_is_the_entire_original_shifted_list
set_option pp.all true in
#check @every_partial_product_pair_producer_can_pause_and_resume_with_its_actual_high_product
#print axioms every_partial_product_pair_producer_can_pause_and_resume_with_its_actual_high_product
set_option pp.all true in
#check @sourcePartialWordMultiply
#print axioms sourcePartialWordMultiply
set_option pp.all true in
#check @every_partial_word_product_can_resume_with_both_its_actual_high_word_and_captured_carry
#print axioms every_partial_word_product_can_resume_with_both_its_actual_high_word_and_captured_carry
set_option pp.all true in
#check @the_original_entire_unsigned_product_is_the_partial_product_followed_by_its_actual_final_adc
#print axioms the_original_entire_unsigned_product_is_the_partial_product_followed_by_its_actual_final_adc
set_option pp.all true in
#check @one_source_partial_product_word_consumes_the_actual_previous_high_and_carry
#print axioms one_source_partial_product_word_consumes_the_actual_previous_high_and_carry
set_option pp.all true in
#check @every_symbolic_partial_product_pair_list_retains_the_entire_input_word_count
#print axioms every_symbolic_partial_product_pair_list_retains_the_entire_input_word_count
set_option pp.all true in
#check @every_partial_word_product_retains_the_entire_input_word_count
#print axioms every_partial_word_product_retains_the_entire_input_word_count
set_option pp.all true in
#check @every_partial_word_product_conserves_the_full_integer_with_both_captured_boundary_values
#print axioms every_partial_word_product_conserves_the_full_integer_with_both_captured_boundary_values
end ShielddSecurity.TransferBlstArmInversePartialProductSplit01
