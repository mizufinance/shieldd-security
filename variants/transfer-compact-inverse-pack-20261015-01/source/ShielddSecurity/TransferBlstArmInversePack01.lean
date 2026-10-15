import Mathlib.Tactic.Ring
import ShielddSecurity.TransferBlstArmInverseFactors01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePack01

/-! Integer interpretation of the locked inner_loop_31 biased factor words.
The two 32-bit slots use bias 0x7fffffff. Subtract/add/double identities are
symbolic. Explicit slot bounds permit decoding; deriving those bounds from
the original loop, approximations and actual ISA execution remains separate. -/

def sourceBiasedPair (f g : Int) : Int :=
  (f+2147483647)+4294967296*(g+2147483647)

def sourceBiasPair : Int := 9223372034707292159

def sourceDecodeLow (word : Int) : Int := word%4294967296-2147483647

def sourceDecodeHigh (word : Int) : Int := word/4294967296-2147483647

theorem original_packed_factor_initialization_is_the_biased_identity_matrix :
    sourceBiasedPair 1 0=9223372034707292160 ∧
    sourceBiasedPair 0 1=9223372039002259455 ∧
    sourceBiasedPair 0 0=sourceBiasPair := by
  decide

theorem original_packed_subtract_and_bias_derives_row_subtraction
    (f g h k : Int) :
    sourceBiasedPair f g-sourceBiasedPair h k+sourceBiasPair=
      sourceBiasedPair (f-h) (g-k) := by
  unfold sourceBiasedPair sourceBiasPair
  ring

theorem original_packed_double_and_bias_derives_row_doubling (f g : Int) :
    2*sourceBiasedPair f g-sourceBiasPair=sourceBiasedPair (2*f) (2*g) := by
  unfold sourceBiasedPair sourceBiasPair
  ring

theorem bounded_original_biased_slots_derive_the_full_unsigned_word_range
    (f g : Int) (lowNonnegative : 0≤f+2147483647) (lowBounded : f+2147483647<4294967296)
    (highNonnegative : 0≤g+2147483647) (highBounded : g+2147483647<4294967296) :
    0≤sourceBiasedPair f g ∧ sourceBiasedPair f g<18446744073709551616 := by
  unfold sourceBiasedPair
  constructor <;> omega

theorem original_biased_slot_extraction_and_bias_removal_recovers_both_coefficients
    (f g : Int) (lowNonnegative : 0≤f+2147483647) (lowBounded : f+2147483647<4294967296) :
    sourceDecodeLow (sourceBiasedPair f g)=f ∧
      sourceDecodeHigh (sourceBiasedPair f g)=g := by
  unfold sourceDecodeLow sourceDecodeHigh sourceBiasedPair
  constructor <;> omega

theorem original_packed_subtract_sequence_has_the_derived_row_residue
    (f g h k : Int) :
    (sourceBiasedPair f g-sourceBiasedPair h k+sourceBiasPair)%18446744073709551616=
      sourceBiasedPair (f-h) (g-k)%18446744073709551616 := by
  rw [original_packed_subtract_and_bias_derives_row_subtraction]

theorem original_packed_double_sequence_has_the_derived_row_residue (f g : Int) :
    (2*sourceBiasedPair f g-sourceBiasPair)%18446744073709551616=
      sourceBiasedPair (2*f) (2*g)%18446744073709551616 := by
  rw [original_packed_double_and_bias_derives_row_doubling]

set_option pp.all true in
#check @sourceBiasedPair
#print axioms sourceBiasedPair
set_option pp.all true in
#check @sourceBiasPair
#print axioms sourceBiasPair
set_option pp.all true in
#check @sourceDecodeLow
#print axioms sourceDecodeLow
set_option pp.all true in
#check @sourceDecodeHigh
#print axioms sourceDecodeHigh
set_option pp.all true in
#check @original_packed_factor_initialization_is_the_biased_identity_matrix
#print axioms original_packed_factor_initialization_is_the_biased_identity_matrix
set_option pp.all true in
#check @original_packed_subtract_and_bias_derives_row_subtraction
#print axioms original_packed_subtract_and_bias_derives_row_subtraction
set_option pp.all true in
#check @original_packed_double_and_bias_derives_row_doubling
#print axioms original_packed_double_and_bias_derives_row_doubling
set_option pp.all true in
#check @bounded_original_biased_slots_derive_the_full_unsigned_word_range
#print axioms bounded_original_biased_slots_derive_the_full_unsigned_word_range
set_option pp.all true in
#check @original_biased_slot_extraction_and_bias_removal_recovers_both_coefficients
#print axioms original_biased_slot_extraction_and_bias_removal_recovers_both_coefficients
set_option pp.all true in
#check @original_packed_subtract_sequence_has_the_derived_row_residue
#print axioms original_packed_subtract_sequence_has_the_derived_row_residue
set_option pp.all true in
#check @original_packed_double_sequence_has_the_derived_row_residue
#print axioms original_packed_double_sequence_has_the_derived_row_residue
end ShielddSecurity.TransferBlstArmInversePack01
