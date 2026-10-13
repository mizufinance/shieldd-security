import ShielddSecurity.TransferBlstArmRedc01
import ShielddSecurity.TransferBlstArmConstructor01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseTail01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)
open TransferBlstArmRedc01 (sourceRedcWords)
open TransferBlstArmNormalized01 (sourceBlstFrWordMeaning)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceRedcWords sourceBlstFrWordMeaning
  TransferBlstArmConstructor01.sourceFrFromLimbs

/-! The original inverse tail consumes arbitrary observed ct-inverse low and
high words through full ARM redc and rRR-left CIOS multiplication. Width and
canonical result are derived, as is the wide-input weighted field relation.
The ct-inverse recurrence and its inverse identity are still open. -/

def sourceRedcVector (low high : Vector UInt64 4) : Vector UInt64 4 :=
  ⟨(sourceRedcWords low high).toArray,by
    rw [List.size_toArray,TransferBlstArmRedc01.original_redc_all_raw_high_words_retain_four_output_words]⟩

theorem original_redc_vector_retains_every_actual_selected_word (low high : Vector UInt64 4) :
    (sourceRedcVector low high).toList = sourceRedcWords low high := by
  simp only [sourceRedcVector,Vector.toList,List.toList_toArray]

def sourceInverseTail (low high : Vector UInt64 4) : CanonicalScalar :=
  TransferBlstArmConstructor01.sourceFrFromLimbs (sourceRedcVector low high)

theorem original_inverse_redc_and_rRR_tail_derives_the_entire_observed_wide_input_field_relation
    (low high : Vector UInt64 4) :
    (radix64^4 : ZMod nullifierModulus) * sourceBlstFrWordMeaning (sourceInverseTail low high).words =
      (packWords low.toList + radix64^4 * packWords high.toList : ZMod nullifierModulus) := by
  have weighted := TransferBlstArmRedc01.original_redc_derives_the_entire_wide_input_weighted_modular_relation low high
  have interpreted := congrArg (fun value : Nat => (value : ZMod nullifierModulus)) weighted
  simp only [ZMod.natCast_mod,Nat.cast_mul,Nat.cast_add] at interpreted
  rw [sourceInverseTail,TransferBlstArmConstructor01.original_locked_constructor_word_meaning_is_the_original_input_field_cast,
    original_redc_vector_retains_every_actual_selected_word]
  exact interpreted

theorem original_inverse_redc_and_rRR_tail_derives_output_canonicality
    (low high : Vector UInt64 4) :
    packWords (sourceInverseTail low high).words.toList < nullifierModulus :=
  (sourceInverseTail low high).canonical

theorem original_inverse_tail_caller_derives_every_result_field_byte
    (low high scratch : Vector UInt64 4) (scalarPrior outputPrior : Vector UInt8 32) (index : Fin 32) :
    (TransferBlstArmCaller01.sourceAsSlice ((sourceInverseTail low high).words,scalarPrior,outputPrior) scratch).2.2[index.val] =
      TransferCommonwareMapBytes01.canonicalBEByte (sourceBlstFrWordMeaning (sourceInverseTail low high).words) index :=
  TransferBlstArmCaller01.caller_as_slice_derives_every_original_input_field_byte _ _ index

set_option pp.all true in
#check @sourceRedcVector
#print axioms sourceRedcVector
set_option pp.all true in
#check @original_redc_vector_retains_every_actual_selected_word
#print axioms original_redc_vector_retains_every_actual_selected_word
set_option pp.all true in
#check @sourceInverseTail
#print axioms sourceInverseTail
set_option pp.all true in
#check @original_inverse_redc_and_rRR_tail_derives_the_entire_observed_wide_input_field_relation
#print axioms original_inverse_redc_and_rRR_tail_derives_the_entire_observed_wide_input_field_relation
set_option pp.all true in
#check @original_inverse_redc_and_rRR_tail_derives_output_canonicality
#print axioms original_inverse_redc_and_rRR_tail_derives_output_canonicality
set_option pp.all true in
#check @original_inverse_tail_caller_derives_every_result_field_byte
#print axioms original_inverse_tail_caller_derives_every_result_field_byte
end ShielddSecurity.TransferBlstArmInverseTail01
