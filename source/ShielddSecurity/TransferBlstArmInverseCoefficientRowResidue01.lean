import ShielddSecurity.TransferBlstArmInverseLowProduct01
import ShielddSecurity.TransferBlstArmInverseWordSum01
import ShielddSecurity.TransferBlstArmInverseSignedProductDecode01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseCoefficientRowResidue01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseLowProduct01 (sourceSignedLowProductWords)
open TransferBlstArmInverseWordSum01 (sourceWordSum)
open TransferBlstArmInverseSignedWord01 (sourceSignedWordMeaning)
open TransferBlstArmInverseSignedProductDecode01 (sourceSignedRadixDecode)
attribute [local irreducible] sourceSignedLowProductWords sourceWordSum sourceSignedWordMeaning

/-! A coefficient word-row program with arbitrary signed factor words and
possibly zero coefficient operands. Modulo-width correctness follows from
actual source low products and carry addition. Signed input correspondence
is explicit; the assembly's split/truncated layouts and final extra word
still require their separate bridge. -/

def sourceCoefficientRowWords (left right : List UInt64) (factors : UInt64 × UInt64) : List UInt64 × Bool :=
  sourceWordSum (sourceSignedLowProductWords left factors.1) (sourceSignedLowProductWords right factors.2)

theorem every_equal_width_source_coefficient_row_retains_the_entire_original_word_count
    (left right : List UInt64) (factors : UInt64 × UInt64) (same : left.length = right.length) :
    (sourceCoefficientRowWords left right factors).1.length = left.length := by
  have widths : (sourceSignedLowProductWords left factors.1).length =
      (sourceSignedLowProductWords right factors.2).length := by
    simp only [TransferBlstArmInverseLowProduct01.every_source_low_word_product_retains_the_entire_original_input_width, same]
  unfold sourceCoefficientRowWords
  rw [TransferBlstArmInverseWordSum01.equal_width_source_word_addition_retains_the_entire_output_width _ _ widths,
    TransferBlstArmInverseLowProduct01.every_source_low_word_product_retains_the_entire_original_input_width]

theorem every_equal_width_source_coefficient_row_derives_the_complete_signed_linear_combination_residue
    (left right : List UInt64) (factors : UInt64 × UInt64) (same : left.length = right.length) :
    (packWords (sourceCoefficientRowWords left right factors).1 : Int) % ((radix64 ^ left.length : Nat) : Int) =
      ((packWords left : Int) * sourceSignedWordMeaning factors.1 +
       (packWords right : Int) * sourceSignedWordMeaning factors.2) % ((radix64 ^ left.length : Nat) : Int) := by
  have widths : (sourceSignedLowProductWords left factors.1).length =
      (sourceSignedLowProductWords right factors.2).length := by
    simp only [TransferBlstArmInverseLowProduct01.every_source_low_word_product_retains_the_entire_original_input_width, same]
  have sum := TransferBlstArmInverseWordSum01.equal_width_source_word_addition_retains_the_full_integer_sum_residue
    (sourceSignedLowProductWords left factors.1) (sourceSignedLowProductWords right factors.2) widths
  rw [TransferBlstArmInverseLowProduct01.every_source_low_word_product_retains_the_entire_original_input_width,
    TransferBlstArmInverseLowProduct01.every_source_factor_word_produces_the_entire_low_product_residue_of_its_actual_signed_meaning,
    TransferBlstArmInverseLowProduct01.every_source_factor_word_produces_the_entire_low_product_residue_of_its_actual_signed_meaning,
    ←same, ← Int.add_emod] at sum
  exact sum

attribute [local irreducible] sourceCoefficientRowWords

theorem equal_entire_input_residues_preserve_every_signed_linear_combination_residue
    (capacity left right a b f g : Int)
    (leftInput : left % capacity = a % capacity) (rightInput : right % capacity = b % capacity) :
    (left * f + right * g) % capacity = (a * f + b * g) % capacity := by
  rw [Int.add_emod, Int.mul_emod, leftInput, Int.mul_emod right, rightInput,
    ← Int.mul_emod, ← Int.mul_emod, ← Int.add_emod]

theorem source_coefficient_words_with_exact_input_residues_derive_the_entire_integer_row_residue
    (left right : List UInt64) (factors : UInt64 × UInt64) (a b : Int) (same : left.length = right.length)
    (leftInput : (packWords left : Int) % ((radix64 ^ left.length : Nat) : Int) = a % ((radix64 ^ left.length : Nat) : Int))
    (rightInput : (packWords right : Int) % ((radix64 ^ left.length : Nat) : Int) = b % ((radix64 ^ left.length : Nat) : Int)) :
    (packWords (sourceCoefficientRowWords left right factors).1 : Int) % ((radix64 ^ left.length : Nat) : Int) =
      (a * sourceSignedWordMeaning factors.1 + b * sourceSignedWordMeaning factors.2) % ((radix64 ^ left.length : Nat) : Int) := by
  exact (every_equal_width_source_coefficient_row_derives_the_complete_signed_linear_combination_residue left right factors same).trans
    (equal_entire_input_residues_preserve_every_signed_linear_combination_residue _ _ _ a b _ _ leftInput rightInput)

theorem bounded_entire_integer_rows_are_recovered_from_the_source_coefficient_word_program
    (left right : List UInt64) (factors : UInt64 × UInt64) (a b half : Int)
    (same : left.length = right.length)
    (capacity : ((radix64 ^ left.length : Nat) : Int) = 2 * half)
    (leftInput : (packWords left : Int) % (2 * half) = a % (2 * half))
    (rightInput : (packWords right : Int) % (2 * half) = b % (2 * half))
    (lower : -half ≤ a * sourceSignedWordMeaning factors.1 + b * sourceSignedWordMeaning factors.2)
    (upper : a * sourceSignedWordMeaning factors.1 + b * sourceSignedWordMeaning factors.2 < half) :
    sourceSignedRadixDecode half (packWords (sourceCoefficientRowWords left right factors).1 : Int) =
      a * sourceSignedWordMeaning factors.1 + b * sourceSignedWordMeaning factors.2 := by
  have unsignedBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power
    (sourceCoefficientRowWords left right factors).1
  rw [every_equal_width_source_coefficient_row_retains_the_entire_original_word_count left right factors same] at unsignedBound
  have unsignedSmall : (packWords (sourceCoefficientRowWords left right factors).1 : Int) < 2 * half := by
    rw [← capacity]
    exact_mod_cast unsignedBound
  rw [← capacity] at leftInput rightInput
  have residue := source_coefficient_words_with_exact_input_residues_derive_the_entire_integer_row_residue
    left right factors a b same leftInput rightInput
  rw [capacity] at residue
  exact TransferBlstArmInverseSignedProductDecode01.exact_residue_and_both_entire_ranges_derive_the_full_signed_integer
    half _ _ (Int.natCast_nonneg _) unsignedSmall lower upper residue

set_option pp.all true in
#check @sourceCoefficientRowWords
#print axioms sourceCoefficientRowWords
set_option pp.all true in
#check @every_equal_width_source_coefficient_row_retains_the_entire_original_word_count
#print axioms every_equal_width_source_coefficient_row_retains_the_entire_original_word_count
set_option pp.all true in
#check @every_equal_width_source_coefficient_row_derives_the_complete_signed_linear_combination_residue
#print axioms every_equal_width_source_coefficient_row_derives_the_complete_signed_linear_combination_residue
set_option pp.all true in
#check @equal_entire_input_residues_preserve_every_signed_linear_combination_residue
#print axioms equal_entire_input_residues_preserve_every_signed_linear_combination_residue
set_option pp.all true in
#check @source_coefficient_words_with_exact_input_residues_derive_the_entire_integer_row_residue
#print axioms source_coefficient_words_with_exact_input_residues_derive_the_entire_integer_row_residue
set_option pp.all true in
#check @bounded_entire_integer_rows_are_recovered_from_the_source_coefficient_word_program
#print axioms bounded_entire_integer_rows_are_recovered_from_the_source_coefficient_word_program
end ShielddSecurity.TransferBlstArmInverseCoefficientRowResidue01
