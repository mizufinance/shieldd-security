import ShielddSecurity.TransferBlstArmSqrtState01
import ShielddSecurity.TransferBlstArmObservedInverse01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmSqrtObserved01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBlstArmNormalized01 (sourceBlstFrWordMeaning)
open TransferBlstArmSqrtWhile01 (sourceCallerZero sourceWordInitial sourceWordSqrt)
open TransferBlstArmSqrtState01 (sourceWordStateMeaning)
attribute [local irreducible] sourceBlstFrWordMeaning
  TransferBlstArmRingCaller01.sourceCallerSqrtSeed TransferBlstArmRingCaller01.sourceCallerSquare
  TransferBlstArmCiosWalk01.sourceCiosProduct

/-! Full word-source sqrt, including zero guard and actual seed/inverse-word
initialization, is the qualified observed-inverse field while. Arbitrary
observed inverse words are preserved as inputs; correctness and native
execution of ct_inverse remain separate. -/

theorem original_zero_word_guard_is_the_original_input_field_zero_guard (input : CanonicalScalar) :
    input.words = sourceCallerZero.words ↔ sourceBlstFrWordMeaning input.words = 0 := by
  constructor
  · intro same
    rw [same,TransferBlstArmSqrtWhile01.original_caller_zero_has_the_exact_zero_field_meaning]
  · intro zero
    have fields := TransferBlstArmRingCaller01.canonical_original_word_field_meaning_is_injective input sourceCallerZero
      (zero.trans TransferBlstArmSqrtWhile01.original_caller_zero_has_the_exact_zero_field_meaning.symm)
    exact congrArg CanonicalScalar.words fields

theorem original_word_initial_state_is_the_exact_observed_inverse_field_state
    (input : CanonicalScalar) (actualInverse : Vector UInt64 4) :
    sourceWordStateMeaning (sourceWordInitial input actualInverse) =
      TransferBlstArmObservedInverse01.sourceObservedInitial input actualInverse := by
  have rootMeaning : sourceBlstFrWordMeaning TransferBlstArmSqrtWhile01.sourceCallerRoot.words =
      TransferCommonwareSqrtComplete01.sourceCommonwareRoot := by
    rw [sourceBlstFrWordMeaning,TransferBlstArmSqrtWhile01.sourceCallerRoot,
      TransferCommonwareSqrtComplete01.sourceCommonwareRoot]
  simp only [sourceWordStateMeaning,sourceWordInitial,
    TransferBlstArmObservedInverse01.sourceObservedInitial,rootMeaning]

theorem complete_original_word_source_sqrt_is_the_qualified_observed_inverse_field_while
    (input : CanonicalScalar) (actualInverse : Vector UInt64 4) :
    (sourceWordSqrt input actualInverse).map (fun value => sourceBlstFrWordMeaning value.words) =
      TransferBlstArmObservedInverse01.sourceObservedInverseFieldWhile input actualInverse := by
  rw [sourceWordSqrt,TransferBlstArmObservedInverse01.sourceObservedInverseFieldWhile]
  by_cases zero : input.words = sourceCallerZero.words
  · have fieldZero := (original_zero_word_guard_is_the_original_input_field_zero_guard input).mp zero
    simp only [if_pos zero,if_pos fieldZero,Option.map_some,
      TransferBlstArmSqrtWhile01.original_caller_zero_has_the_exact_zero_field_meaning]
  · have fieldNonzero : sourceBlstFrWordMeaning input.words ≠ 0 :=
      fun impossible => zero ((original_zero_word_guard_is_the_original_input_field_zero_guard input).mpr impossible)
    simp only [if_neg zero,if_neg fieldNonzero]
    rw [TransferBlstArmSqrtState01.complete_original_decreasing_word_while_is_the_qualified_field_while
      input (sourceWordInitial input actualInverse) (by change 1 ≤ 32; decide),
      original_word_initial_state_is_the_exact_observed_inverse_field_state]

set_option pp.all true in
#check @original_zero_word_guard_is_the_original_input_field_zero_guard
#print axioms original_zero_word_guard_is_the_original_input_field_zero_guard
set_option pp.all true in
#check @original_word_initial_state_is_the_exact_observed_inverse_field_state
#print axioms original_word_initial_state_is_the_exact_observed_inverse_field_state
set_option pp.all true in
#check @complete_original_word_source_sqrt_is_the_qualified_observed_inverse_field_while
#print axioms complete_original_word_source_sqrt_is_the_qualified_observed_inverse_field_while
end ShielddSecurity.TransferBlstArmSqrtObserved01
