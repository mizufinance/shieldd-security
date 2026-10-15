import ShielddSecurity.TransferBlstArmInverseOriginalRowMagnitude01
import ShielddSecurity.TransferBlstArmInverseMagnitudeBatch01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordMagnitudeBatch01
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseWordRepack01 (sourceFourWordsOfNat)
open TransferBlstArmInverseMagnitudeBatch01 (sourceMagnitudeBatch)
open TransferBlstArmInverseOriginalRowMagnitude01 (sourceOriginalRowMagnitudeWords sourceOriginalRowQuotient)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
attribute [local irreducible] sourceFourWordsOfNat sourceOriginalRowMagnitudeWords sourceOriginalRowQuotient sourceActualFactorQuotients

/-! Both source word-operation rows, after the original input repacking,
return exactly the existing full-integer magnitude-batch model. This closes
the arithmetic source operations to that batch recurrence. Packed factor
register origins, accumulated coefficient words and native execution remain open. -/

def sourceMagnitudeWordBatch (input : Nat × Nat) : List UInt64 × List UInt64 :=
  let a := sourceFourWordsOfNat input.1
  let b := sourceFourWordsOfNat input.2
  ((sourceOriginalRowMagnitudeWords false a b).1, (sourceOriginalRowMagnitudeWords true a b).1)

theorem both_symbolic_row_equalities_derive_the_entire_output_pair
    (output : Bool → Nat) (actual : Int × Int)
    (rows : ∀ second, output second = (if second then actual.2 else actual.1).natAbs) :
    (output false, output true) = (actual.1.natAbs, actual.2.natAbs) := by
  exact Prod.ext (rows false) (rows true)

theorem original_repacked_signed_word_operations_derive_both_complete_magnitude_batch_outputs
    (input : Nat × Nat) (odd : input.2 % 2 = 1) :
    (packWords (sourceMagnitudeWordBatch input).1, packWords (sourceMagnitudeWordBatch input).2) = sourceMagnitudeBatch input := by
  let a := sourceFourWordsOfNat input.1
  let b := sourceFourWordsOfNat input.2
  have lowOdd := TransferBlstArmInverseWordRepack01.an_odd_natural_input_has_an_odd_original_repacked_low_word input.2 odd
  let actual := sourceActualFactorQuotients 31
    (TransferBlstArmInverseApproxBits01.sourceApproxLow31
      (TransferBlstArmInverseWindowInput01.sourceFourWordWindowWords a b).1 a.w0)
    (TransferBlstArmInverseApproxBits01.sourceApproxLow31
      (TransferBlstArmInverseWindowInput01.sourceFourWordWindowWords a b).2 b.w0)
    (TransferBlstArmInverseWindowSelect01.sourcePackedFourWords a : Int)
    (TransferBlstArmInverseWindowSelect01.sourcePackedFourWords b : Int)
  have rows : ∀ second, packWords (sourceOriginalRowMagnitudeWords second a b).1 =
      (if second then actual.2 else actual.1).natAbs := by
    intro second
    have result := TransferBlstArmInverseOriginalRowMagnitude01.original_source_signed_products_carry_extr_asr_and_absolute_correction_derive_the_entire_quotient_magnitude second a b lowOdd
    rw [TransferBlstArmInverseOriginalRowMagnitude01.the_original_selected_row_quotient_is_the_original_full_input_quotient] at result
    exact result
  have complete := both_symbolic_row_equalities_derive_the_entire_output_pair
    (fun second => packWords (sourceOriginalRowMagnitudeWords second a b).1) actual rows
  unfold sourceMagnitudeWordBatch sourceMagnitudeBatch
  exact complete

set_option pp.all true in
#check @sourceMagnitudeWordBatch
#print axioms sourceMagnitudeWordBatch
set_option pp.all true in
#check @both_symbolic_row_equalities_derive_the_entire_output_pair
#print axioms both_symbolic_row_equalities_derive_the_entire_output_pair
set_option pp.all true in
#check @original_repacked_signed_word_operations_derive_both_complete_magnitude_batch_outputs
#print axioms original_repacked_signed_word_operations_derive_both_complete_magnitude_batch_outputs
end ShielddSecurity.TransferBlstArmInverseWordMagnitudeBatch01
