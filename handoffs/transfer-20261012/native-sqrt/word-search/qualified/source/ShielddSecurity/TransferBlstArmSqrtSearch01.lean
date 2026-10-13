import ShielddSecurity.TransferBlstArmRingCaller01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmSqrtSearch01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBlstArmRingCaller01 (sourceCallerOne sourceCallerSquare)
open TransferBlstArmNormalized01 (sourceBlstFrWordMeaning)
open TransferBoundedNativeCodec01 (nullifierModulus)
attribute [local irreducible] sourceCallerOne sourceCallerSquare sourceBlstFrWordMeaning
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

/-! Original typed-word inner sqrt search checks original words against the
original one constant, squares through actual default clone+CIOS multiplication,
increments i, and refuses at i==m after the square. Its complete symbolic walk
is the qualified field search; every successful index is below m, and the
actual UInt32 increment has no wrap for m<=32. Compiler/ISA/Clone/alias and
private input producers remain separate, and no desired search index is given. -/

theorem original_word_unit_comparison_is_exact_original_field_unit_comparison (value : CanonicalScalar) :
    value.words = sourceCallerOne.words ↔ sourceBlstFrWordMeaning value.words = 1 := by
  constructor
  · intro same
    rw [same,TransferBlstArmRingCaller01.original_blst_fr_one_words_have_exact_original_field_value]
  · intro same
    have fields : value = sourceCallerOne :=
      TransferBlstArmRingCaller01.canonical_original_word_field_meaning_is_injective value sourceCallerOne
        (same.trans TransferBlstArmRingCaller01.original_blst_fr_one_words_have_exact_original_field_value.symm)
    exact congrArg CanonicalScalar.words fields

def sourceWordSearchWalk (m : Nat) : Nat → Nat → CanonicalScalar → Option Nat
  | 0,_,_ => none
  | fuel+1,index,value =>
      if value.words = sourceCallerOne.words then some index
      else if index+1=m then none
      else sourceWordSearchWalk m fuel (index+1) (sourceCallerSquare value)

theorem complete_original_word_search_walk_is_the_qualified_original_field_search
    (m fuel index : Nat) (value : CanonicalScalar) :
    sourceWordSearchWalk m fuel index value = TransferCommonwareSqrtSearch01.searchWalk
      m fuel index (sourceBlstFrWordMeaning value.words) := by
  induction fuel generalizing index value with
  | zero => rfl
  | succ fuel ih =>
      by_cases unit : value.words = sourceCallerOne.words
      · have fieldUnit := (original_word_unit_comparison_is_exact_original_field_unit_comparison value).mp unit
        simp only [sourceWordSearchWalk,TransferCommonwareSqrtSearch01.searchWalk,if_pos unit,if_pos fieldUnit]
      · have fieldNonunit : sourceBlstFrWordMeaning value.words ≠ 1 := by
          intro impossible
          exact unit ((original_word_unit_comparison_is_exact_original_field_unit_comparison value).mpr impossible)
        rw [sourceWordSearchWalk,TransferCommonwareSqrtSearch01.searchWalk,if_neg unit,if_neg fieldNonunit]
        by_cases boundary : index+1=m
        · simp only [if_pos boundary]
        · simp only [if_neg boundary]
          rw [ih,TransferBlstArmRingCaller01.original_default_square_caller_derives_the_original_input_field_square,pow_two]

def sourceWordSearch (m : Nat) (value : CanonicalScalar) : Option Nat := sourceWordSearchWalk m m 0 value

theorem actual_original_word_inner_search_is_the_qualified_source_search (m : Nat) (value : CanonicalScalar) :
    sourceWordSearch m value = TransferCommonwareSqrtSearch01.sourceSearch m (sourceBlstFrWordMeaning value.words) := by
  exact complete_original_word_search_walk_is_the_qualified_original_field_search m m 0 value

theorem returned_original_word_inner_search_derives_the_actual_schedule_bounds
    (m index : Nat) (value : CanonicalScalar) (nonunit : value.words ≠ sourceCallerOne.words)
    (returned : sourceWordSearch m value = some index) : 1 ≤ index ∧ index < m := by
  rw [actual_original_word_inner_search_is_the_qualified_source_search] at returned
  have fieldNonunit : sourceBlstFrWordMeaning value.words ≠ 1 := by
    intro impossible
    exact nonunit ((original_word_unit_comparison_is_exact_original_field_unit_comparison value).mpr impossible)
  exact ⟨TransferCommonwareSqrtSchedule01.every_successful_nonunit_source_search_returns_a_positive_index
    m index _ fieldNonunit returned,
    TransferCommonwareSqrtSchedule01.every_successful_source_search_returns_an_index_below_m m index _ returned⟩

def sourceWordRepeatedSquare : Nat → CanonicalScalar → CanonicalScalar
  | 0,value => value
  | count+1,value => sourceWordRepeatedSquare count (sourceCallerSquare value)

theorem original_word_correction_square_walk_is_the_qualified_field_square_walk
    (count : Nat) (value : CanonicalScalar) :
    sourceBlstFrWordMeaning (sourceWordRepeatedSquare count value).words =
      TransferCommonwareSqrtSearch01.squareWalk count (sourceBlstFrWordMeaning value.words) := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih =>
      rw [sourceWordRepeatedSquare,TransferCommonwareSqrtSearch01.squareWalk,ih,
        TransferBlstArmRingCaller01.original_default_square_caller_derives_the_original_input_field_square,pow_two]
set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @original_word_unit_comparison_is_exact_original_field_unit_comparison
#print axioms original_word_unit_comparison_is_exact_original_field_unit_comparison
set_option pp.all true in
#check @sourceWordSearchWalk
#print axioms sourceWordSearchWalk
set_option pp.all true in
#check @complete_original_word_search_walk_is_the_qualified_original_field_search
#print axioms complete_original_word_search_walk_is_the_qualified_original_field_search
set_option pp.all true in
#check @sourceWordSearch
#print axioms sourceWordSearch
set_option pp.all true in
#check @actual_original_word_inner_search_is_the_qualified_source_search
#print axioms actual_original_word_inner_search_is_the_qualified_source_search
set_option pp.all true in
#check @returned_original_word_inner_search_derives_the_actual_schedule_bounds
#print axioms returned_original_word_inner_search_derives_the_actual_schedule_bounds
set_option pp.all true in
#check @sourceWordRepeatedSquare
#print axioms sourceWordRepeatedSquare
set_option pp.all true in
#check @original_word_correction_square_walk_is_the_qualified_field_square_walk
#print axioms original_word_correction_square_walk_is_the_qualified_field_square_walk
end ShielddSecurity.TransferBlstArmSqrtSearch01
