import ShielddSecurity.TransferBlstArmRingCaller01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmObservedInverse01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBlstArmNormalized01 (sourceBlstFrWordMeaning)
open TransferBlstArmRingCaller01 (sourceCallerSqrtSeed sourceCallerSquare)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceBlstFrWordMeaning sourceCallerSqrtSeed sourceCallerSquare
  TransferBlstArmCiosWalk01.sourceCiosProduct
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

/-! Original CIOS word seed and square consume the actual observed inverse
four words, with no desired inverse value/range supplied. CIOS accepts arbitrary
right words with the derived canonical left operand and derives a canonical t.
The qualified field while interpretation retains the original final square
check. Returned-root soundness follows even for an incorrect inverse observation;
QR completeness and the full native sqrt contract still require the real
ct-inverse path and word/field loop/native execution correspondence. This is
field-while interpretation evidence, not a native inverse implementation proof. -/

def sourceObservedInitial (input : CanonicalScalar) (actualInverse : Vector UInt64 4) :
    FfFinishedPhase296.State (ZMod nullifierModulus) :=
  let root := sourceCallerSqrtSeed input
  let residue := TransferBlstArmCiosWalk01.sourceCiosProduct (sourceCallerSquare root) actualInverse
  ⟨sourceBlstFrWordMeaning root.words,sourceBlstFrWordMeaning residue.words,
    TransferCommonwareSqrtComplete01.sourceCommonwareRoot,32⟩

theorem original_word_seed_square_and_actual_inverse_words_derive_the_initial_field_state
    (input : CanonicalScalar) (actualInverse : Vector UInt64 4) :
    sourceObservedInitial input actualInverse =
      ⟨(sourceBlstFrWordMeaning input.words)^
          TransferScalarWordPrimitives01.packWords TransferCommonwareSqrtComplete01.sourceCommonwareExponent.toList,
        ((sourceBlstFrWordMeaning input.words)^
          TransferScalarWordPrimitives01.packWords TransferCommonwareSqrtComplete01.sourceCommonwareExponent.toList)^2 *
            sourceBlstFrWordMeaning actualInverse,
        TransferCommonwareSqrtComplete01.sourceCommonwareRoot,32⟩ := by
  simp only [sourceObservedInitial,
    TransferBlstArmCiosWalk01.actual_original_cios_program_derives_the_two_original_input_field_values_product,
    TransferBlstArmRingCaller01.original_default_square_caller_derives_the_original_input_field_square,
    TransferBlstArmRingCaller01.original_word_multiply_square_and_bit_iterator_derive_the_actual_original_sqrt_seed_value]

def sourceObservedInverseFieldWhile (input : CanonicalScalar) (actualInverse : Vector UInt64 4) :
    Option (ZMod nullifierModulus) :=
  if sourceBlstFrWordMeaning input.words = 0 then some 0
  else TransferCommonwareSqrtSchedule01.sourceWhile (sourceBlstFrWordMeaning input.words)
    (sourceObservedInitial input actualInverse)

theorem returned_observed_inverse_field_while_derives_original_input_square_without_inverse_correctness
    (input : CanonicalScalar) (actualInverse : Vector UInt64 4) (returned : ZMod nullifierModulus)
    (success : sourceObservedInverseFieldWhile input actualInverse = some returned) :
    returned^2 = sourceBlstFrWordMeaning input.words := by
  by_cases zero : sourceBlstFrWordMeaning input.words = 0
  · rw [sourceObservedInverseFieldWhile,if_pos zero] at success
    have same : returned=0 := (Option.some.inj success).symm
    rw [same,zero,zero_pow (by decide : 2 ≠ 0)]
  · rw [sourceObservedInverseFieldWhile,if_neg zero] at success
    have budget := TransferCommonwareSqrtSchedule01.actual_budgeted_loop_agrees_with_the_well_founded_source_while
      (sourceBlstFrWordMeaning input.words) 32 (sourceObservedInitial input actualInverse)
      (by change 1 ≤ 32; decide) (by change 32 ≤ 32; decide)
    have executed : TransferCommonwareSqrtLoop01.sourceLoop (sourceBlstFrWordMeaning input.words) 32
        (sourceObservedInitial input actualInverse) = some returned := budget.trans success
    rw [pow_two]
    exact TransferCommonwareSqrtLoop01.every_commonware_loop_success_has_the_checked_root
      (sourceBlstFrWordMeaning input.words) 32 (sourceObservedInitial input actualInverse) returned executed
set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @sourceObservedInitial
#print axioms sourceObservedInitial
set_option pp.all true in
#check @original_word_seed_square_and_actual_inverse_words_derive_the_initial_field_state
#print axioms original_word_seed_square_and_actual_inverse_words_derive_the_initial_field_state
set_option pp.all true in
#check @sourceObservedInverseFieldWhile
#print axioms sourceObservedInverseFieldWhile
set_option pp.all true in
#check @returned_observed_inverse_field_while_derives_original_input_square_without_inverse_correctness
#print axioms returned_observed_inverse_field_while_derives_original_input_square_without_inverse_correctness
end ShielddSecurity.TransferBlstArmObservedInverse01
