import ShielddSecurity.TransferBlstArmInverseSecond01
import ShielddSecurity.TransferBlstArmInverseTail01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePipeline01
open TransferBlstArmInverseFirst01 (WideState sourceWideMeaning sourceWideRaw sourceFirstWordCorrection)
open TransferBlstArmInverseSecond01 (sourceSecondWordCorrection)
open TransferBlstArmInverseSign01 (sourceWideRadix)
open TransferBlstArmNormalized01 (sourceBlstFrWordMeaning)
open TransferBlstArmInverseTail01 (sourceInverseTail)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceInverseTail sourceBlstFrWordMeaning

/-! Full observed inverse coefficient pipeline: two original signed word
adjustments, wide redc and rRR-left CIOS. Output canonicality and weighted
field value follow from those operations. Coefficient production, matrix
termination and actual native execution remain distinct obligations. -/

def sourceCorrectedState (s : WideState) : WideState := sourceSecondWordCorrection (sourceFirstWordCorrection s)
def sourceCorrectedInverse (s : WideState) : CanonicalScalar :=
  sourceInverseTail (sourceCorrectedState s).1 (sourceCorrectedState s).2.1

theorem original_corrected_word_state_derives_the_original_coefficient_field_residue (s : WideState)
    (lower : -sourceWideRadix≤sourceWideMeaning s) (upper : sourceWideMeaning s≤sourceWideRadix) :
    (sourceWideMeaning (sourceCorrectedState s):ZMod nullifierModulus)=(sourceWideMeaning s:ZMod nullifierModulus) := by
  have words := TransferBlstArmInverseSecond01.original_complete_two_word_adjustments_are_the_qualified_integer_signed_correction s lower upper
  change sourceWideMeaning (sourceCorrectedState s)=TransferBlstArmInverseSign01.sourceSignedCorrection (sourceWideMeaning s) at words
  rw [words]
  exact TransferBlstArmInverseSign01.original_two_signed_adjustments_retain_the_original_coefficient_field_residue _

theorem original_corrected_state_signed_meaning_is_its_stored_unsigned_word_cast (s : WideState) :
    (sourceWideMeaning (sourceCorrectedState s):ZMod nullifierModulus)=
      (sourceWideRaw (sourceCorrectedState s):ZMod nullifierModulus) := by
  have top : (sourceCorrectedState s).2.2=0 := by rfl
  rw [sourceWideMeaning,top,mul_zero,add_zero]
  norm_cast

theorem original_full_inverse_word_pipeline_derives_the_entire_observed_coefficient_field_relation (s : WideState)
    (lower : -sourceWideRadix≤sourceWideMeaning s) (upper : sourceWideMeaning s≤sourceWideRadix) :
    (radix64^4:ZMod nullifierModulus)*sourceBlstFrWordMeaning (sourceCorrectedInverse s).words=
      (sourceWideMeaning s:ZMod nullifierModulus) := by
  have tail := TransferBlstArmInverseTail01.original_inverse_redc_and_rRR_tail_derives_the_entire_observed_wide_input_field_relation
    (sourceCorrectedState s).1 (sourceCorrectedState s).2.1
  have raw : (sourceWideRaw (sourceCorrectedState s):ZMod nullifierModulus)=
      (packWords (sourceCorrectedState s).1.toList+radix64^4*packWords (sourceCorrectedState s).2.1.toList:ZMod nullifierModulus) := by
    rw [sourceWideRaw,TransferBlstArmInverseFirst01.symbolic_word_append_has_the_entire_radix_weighted_value,Vector.length_toList]
    norm_cast
  change (radix64^4:ZMod nullifierModulus)*sourceBlstFrWordMeaning (sourceCorrectedInverse s).words=_ at tail
  exact tail.trans (raw.symm.trans ((original_corrected_state_signed_meaning_is_its_stored_unsigned_word_cast s).symm.trans
    (original_corrected_word_state_derives_the_original_coefficient_field_residue s lower upper)))

theorem original_full_inverse_word_pipeline_derives_output_canonicality (s : WideState) :
    packWords (sourceCorrectedInverse s).words.toList<nullifierModulus := (sourceCorrectedInverse s).canonical

set_option pp.all true in
#check @sourceCorrectedState
#print axioms sourceCorrectedState
set_option pp.all true in
#check @sourceCorrectedInverse
#print axioms sourceCorrectedInverse
set_option pp.all true in
#check @original_corrected_word_state_derives_the_original_coefficient_field_residue
#print axioms original_corrected_word_state_derives_the_original_coefficient_field_residue
set_option pp.all true in
#check @original_corrected_state_signed_meaning_is_its_stored_unsigned_word_cast
#print axioms original_corrected_state_signed_meaning_is_its_stored_unsigned_word_cast
set_option pp.all true in
#check @original_full_inverse_word_pipeline_derives_the_entire_observed_coefficient_field_relation
#print axioms original_full_inverse_word_pipeline_derives_the_entire_observed_coefficient_field_relation
set_option pp.all true in
#check @original_full_inverse_word_pipeline_derives_output_canonicality
#print axioms original_full_inverse_word_pipeline_derives_output_canonicality
end ShielddSecurity.TransferBlstArmInversePipeline01
