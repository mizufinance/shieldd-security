import ShielddSecurity.TransferBlstArmSqrtWhile01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmSqrtState01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBlstArmSqrtWhile01 (WordState sourceCheckedRoot sourceWordLoop sourceWordWhile sourceWordUpdate)
open TransferBlstArmNormalized01 (sourceBlstFrWordMeaning)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceBlstFrWordMeaning
  TransferBlstArmRingCaller01.sourceArmMul TransferBlstArmRingCaller01.sourceCallerSquare
  TransferBlstArmSqrtSearch01.sourceWordRepeatedSquare
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

/-! The complete original word-state recurrence maps to the qualified field
recurrence, including refusal and final checked-root branches. State values
and recursive results are derived from original CIOS operations. This closes
the word/field loop interpretation, not ct-inverse or native execution. -/

def sourceWordStateMeaning (state : WordState) : FfFinishedPhase296.State (ZMod nullifierModulus) :=
  ⟨sourceBlstFrWordMeaning state.1.words,sourceBlstFrWordMeaning state.2.1.words,
    sourceBlstFrWordMeaning state.2.2.1.words,state.2.2.2⟩

theorem original_final_word_equality_is_the_exact_original_input_field_square_check
    (input candidate : CanonicalScalar) :
    (TransferBlstArmRingCaller01.sourceCallerSquare candidate).words = input.words ↔
      sourceBlstFrWordMeaning candidate.words * sourceBlstFrWordMeaning candidate.words = sourceBlstFrWordMeaning input.words := by
  constructor
  · intro same
    have values := congrArg sourceBlstFrWordMeaning same
    simpa only [TransferBlstArmRingCaller01.original_default_square_caller_derives_the_original_input_field_square,pow_two] using values
  · intro checked
    have fields : TransferBlstArmRingCaller01.sourceCallerSquare candidate = input :=
      TransferBlstArmRingCaller01.canonical_original_word_field_meaning_is_injective _ _
        (by simpa only [TransferBlstArmRingCaller01.original_default_square_caller_derives_the_original_input_field_square,pow_two] using checked)
    exact congrArg CanonicalScalar.words fields

theorem complete_original_word_final_check_is_the_qualified_field_final_check
    (input candidate : CanonicalScalar) :
    (sourceCheckedRoot input candidate).map (fun value => sourceBlstFrWordMeaning value.words) =
      if sourceBlstFrWordMeaning candidate.words * sourceBlstFrWordMeaning candidate.words = sourceBlstFrWordMeaning input.words
        then some (sourceBlstFrWordMeaning candidate.words) else none := by
  rw [sourceCheckedRoot]
  by_cases checked : (TransferBlstArmRingCaller01.sourceCallerSquare candidate).words = input.words
  · have interpreted := (original_final_word_equality_is_the_exact_original_input_field_square_check input candidate).mp checked
    simp only [if_pos checked,if_pos interpreted,Option.map_some]
  · have refused : sourceBlstFrWordMeaning candidate.words * sourceBlstFrWordMeaning candidate.words ≠ sourceBlstFrWordMeaning input.words :=
      fun possible => checked ((original_final_word_equality_is_the_exact_original_input_field_square_check input candidate).mpr possible)
    simp only [if_neg checked,if_neg refused,Option.map_none]

theorem complete_original_word_update_derives_the_qualified_field_state_update
    (state : WordState) (index : Nat) :
    sourceWordStateMeaning (sourceWordUpdate state index) =
      TransferCommonwareSqrtLoop01.sourceUpdate (sourceWordStateMeaning state) index := by
  simp only [sourceWordStateMeaning,sourceWordUpdate,TransferCommonwareSqrtLoop01.sourceUpdate,
    TransferBlstArmRingCaller01.source_caller_multiply_derives_the_two_original_field_values_product,
    TransferBlstArmRingCaller01.original_default_square_caller_derives_the_original_input_field_square,
    TransferBlstArmSqrtSearch01.original_word_correction_square_walk_is_the_qualified_field_square_walk,pow_two]

theorem complete_original_word_loop_is_the_qualified_original_field_loop
    (input : CanonicalScalar) (fuel : Nat) (state : WordState) :
    (sourceWordLoop input fuel state).map (fun value => sourceBlstFrWordMeaning value.words) =
      TransferCommonwareSqrtLoop01.sourceLoop (sourceBlstFrWordMeaning input.words) fuel (sourceWordStateMeaning state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rw [sourceWordLoop,TransferCommonwareSqrtLoop01.sourceLoop]
      by_cases unit : state.2.1.words = TransferBlstArmRingCaller01.sourceCallerOne.words
      · have interpreted := (TransferBlstArmSqrtSearch01.original_word_unit_comparison_is_exact_original_field_unit_comparison state.2.1).mp unit
        simp only [if_pos unit,sourceWordStateMeaning,if_pos interpreted]
        exact complete_original_word_final_check_is_the_qualified_field_final_check input state.1
      · have nonunit : sourceBlstFrWordMeaning state.2.1.words ≠ 1 :=
          fun possible => unit ((TransferBlstArmSqrtSearch01.original_word_unit_comparison_is_exact_original_field_unit_comparison state.2.1).mpr possible)
        simp only [if_neg unit,sourceWordStateMeaning,if_neg nonunit]
        cases found : TransferBlstArmSqrtSearch01.sourceWordSearch state.2.2.2 state.2.1 with
        | none =>
            have fieldFound := (TransferBlstArmSqrtSearch01.actual_original_word_inner_search_is_the_qualified_source_search state.2.2.2 state.2.1).symm.trans found
            simp only [fieldFound,Option.bind_none,Option.map_none]
        | some index =>
            have fieldFound := (TransferBlstArmSqrtSearch01.actual_original_word_inner_search_is_the_qualified_source_search state.2.2.2 state.2.1).symm.trans found
            simp only [fieldFound,Option.bind_some]
            rw [ih,complete_original_word_update_derives_the_qualified_field_state_update,sourceWordStateMeaning]

theorem complete_original_decreasing_word_while_is_the_qualified_field_while
    (input : CanonicalScalar) (state : WordState) (positive : 1 ≤ state.2.2.2) :
    (sourceWordWhile input state).map (fun value => sourceBlstFrWordMeaning value.words) =
      TransferCommonwareSqrtSchedule01.sourceWhile (sourceBlstFrWordMeaning input.words) (sourceWordStateMeaning state) := by
  have wordBudget := TransferBlstArmSqrtWhile01.original_bounded_word_loop_agrees_with_actual_decreasing_word_while
    input state.2.2.2 state positive (Nat.le_refl _)
  rw [← wordBudget,complete_original_word_loop_is_the_qualified_original_field_loop]
  exact TransferCommonwareSqrtSchedule01.actual_budgeted_loop_agrees_with_the_well_founded_source_while
    (sourceBlstFrWordMeaning input.words) state.2.2.2 (sourceWordStateMeaning state) positive (Nat.le_refl _)

set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @sourceWordStateMeaning
#print axioms sourceWordStateMeaning
set_option pp.all true in
#check @original_final_word_equality_is_the_exact_original_input_field_square_check
#print axioms original_final_word_equality_is_the_exact_original_input_field_square_check
set_option pp.all true in
#check @complete_original_word_final_check_is_the_qualified_field_final_check
#print axioms complete_original_word_final_check_is_the_qualified_field_final_check
set_option pp.all true in
#check @complete_original_word_update_derives_the_qualified_field_state_update
#print axioms complete_original_word_update_derives_the_qualified_field_state_update
set_option pp.all true in
#check @complete_original_word_loop_is_the_qualified_original_field_loop
#print axioms complete_original_word_loop_is_the_qualified_original_field_loop
set_option pp.all true in
#check @complete_original_decreasing_word_while_is_the_qualified_field_while
#print axioms complete_original_decreasing_word_while_is_the_qualified_field_while
end ShielddSecurity.TransferBlstArmSqrtState01
