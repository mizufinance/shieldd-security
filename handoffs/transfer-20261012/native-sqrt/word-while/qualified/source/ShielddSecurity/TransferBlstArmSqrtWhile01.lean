import ShielddSecurity.TransferBlstArmSqrtSearch01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmSqrtWhile01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferBlstArmRingCaller01 (sourceCallerOne sourceArmMul sourceCallerSquare sourceCallerSqrtSeed)
open TransferBlstArmSqrtSearch01 (sourceWordSearch sourceWordRepeatedSquare)
open TransferBlstArmNormalized01 (sourceBlstFrWordMeaning)
attribute [local irreducible] sourceArmMul sourceCallerSquare sourceCallerSqrtSeed sourceBlstFrWordMeaning

local instance scalarPrimeFact : Fact (Nat.Prime TransferBoundedNativeCodec01.nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero TransferBoundedNativeCodec01.nullifierModulus := ⟨by decide⟩

/-! Source word-state while uses exact CIOS clone/multiply/square, original
word equality, actual inner search and correction count. Successful search
derives decreasing m, so the source while has no supplied traversal budget.
Original seed initializes r, while t consumes arbitrary actual inverse words.
Returned complete word-source sqrt derives the original input square solely
through its actual final square check, without a desired inverse/root/output
premise. Native producer/Clone/pointer/UInt32/compiler/ISA and inverse QR
completeness remain distinct obligations. No machine-native/certification credit. -/

abbrev WordState := CanonicalScalar × CanonicalScalar × CanonicalScalar × Nat

def sourceWordUpdate (state : WordState) (index : Nat) : WordState :=
  let correction := sourceWordRepeatedSquare (state.2.2.2-index-1) state.2.2.1
  let nextC := sourceCallerSquare correction
  (sourceArmMul state.1 correction,sourceArmMul state.2.1 nextC,nextC,index)

def sourceCheckedRoot (input candidate : CanonicalScalar) : Option CanonicalScalar :=
  if (sourceCallerSquare candidate).words = input.words then some candidate else none

theorem returned_original_word_final_check_derives_original_input_square
    (input candidate returned : CanonicalScalar) (success : sourceCheckedRoot input candidate = some returned) :
    sourceBlstFrWordMeaning returned.words^2 = sourceBlstFrWordMeaning input.words := by
  unfold sourceCheckedRoot at success
  split at success
  next checked =>
    have same := Option.some.inj success
    subst returned
    have wordValue := congrArg sourceBlstFrWordMeaning checked
    rw [TransferBlstArmRingCaller01.original_default_square_caller_derives_the_original_input_field_square] at wordValue
    exact wordValue
  next refused => cases success

def sourceWordLoop (input : CanonicalScalar) : Nat → WordState → Option CanonicalScalar
  | 0,_ => none
  | fuel+1,state =>
      if state.2.1.words = sourceCallerOne.words then sourceCheckedRoot input state.1
      else (sourceWordSearch state.2.2.2 state.2.1).bind
        (fun index => sourceWordLoop input fuel (sourceWordUpdate state index))

theorem returned_original_word_loop_derives_original_input_square
    (input returned : CanonicalScalar) (fuel : Nat) (state : WordState)
    (success : sourceWordLoop input fuel state = some returned) :
    sourceBlstFrWordMeaning returned.words^2 = sourceBlstFrWordMeaning input.words := by
  induction fuel generalizing state with
  | zero => cases success
  | succ fuel ih =>
      rw [sourceWordLoop] at success
      split at success
      next unit => exact returned_original_word_final_check_derives_original_input_square input state.1 returned success
      next nonunit =>
        cases found : sourceWordSearch state.2.2.2 state.2.1 with
        | none => simp only [found,Option.bind_none] at success; cases success
        | some index =>
            exact ih (sourceWordUpdate state index) (by simpa only [found,Option.bind_some] using success)

def sourceWordWhile (input : CanonicalScalar) (state : WordState) : Option CanonicalScalar :=
  if state.2.1.words = sourceCallerOne.words then sourceCheckedRoot input state.1
  else match _found : sourceWordSearch state.2.2.2 state.2.1 with
    | none => none
    | some index => sourceWordWhile input (sourceWordUpdate state index)
termination_by state.2.2.2
decreasing_by
  change index < state.2.2.2
  have fieldFound := (TransferBlstArmSqrtSearch01.actual_original_word_inner_search_is_the_qualified_source_search
    state.2.2.2 state.2.1).symm.trans _found
  exact TransferCommonwareSqrtSchedule01.every_successful_source_search_returns_an_index_below_m
    state.2.2.2 index (sourceBlstFrWordMeaning state.2.1.words) fieldFound

theorem original_bounded_word_loop_agrees_with_actual_decreasing_word_while
    (input : CanonicalScalar) (fuel : Nat) (state : WordState)
    (positive : 1 ≤ state.2.2.2) (bounded : state.2.2.2 ≤ fuel) :
    sourceWordLoop input fuel state = sourceWordWhile input state := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      rw [sourceWordLoop,sourceWordWhile]
      by_cases unit : state.2.1.words = sourceCallerOne.words
      · simp only [if_pos unit]
      · simp only [if_neg unit]
        cases found : sourceWordSearch state.2.2.2 state.2.1 with
        | none => simp only [Option.bind_none]
        | some index =>
            simp only [Option.bind_some]
            have bounds := TransferBlstArmSqrtSearch01.returned_original_word_inner_search_derives_the_actual_schedule_bounds
              state.2.2.2 index state.2.1 unit found
            exact ih (sourceWordUpdate state index) bounds.1 (by change index ≤ fuel; omega)

def sourceCallerRoot : CanonicalScalar :=
  ⟨#v[0xb9b58d8c5f0e466a,0x5b1b4c801819d7ec,0x0af53ae352a31e64,0x5bf3adda19e9b27b],by decide⟩

def sourceCallerZero : CanonicalScalar := ⟨#v[0,0,0,0],by decide⟩

theorem original_caller_zero_has_the_exact_zero_field_meaning :
    sourceBlstFrWordMeaning sourceCallerZero.words = 0 := by
  rw [sourceBlstFrWordMeaning,TransferScalarMontgomeryValue01.montgomeryValue]
  decide

def sourceWordInitial (input : CanonicalScalar) (actualInverse : Vector UInt64 4) : WordState :=
  let root := sourceCallerSqrtSeed input
  let residue := TransferBlstArmCiosWalk01.sourceCiosProduct (sourceCallerSquare root) actualInverse
  (root,residue,sourceCallerRoot,32)

def sourceWordSqrt (input : CanonicalScalar) (actualInverse : Vector UInt64 4) : Option CanonicalScalar :=
  if input.words = sourceCallerZero.words then some sourceCallerZero
  else sourceWordWhile input (sourceWordInitial input actualInverse)

theorem returned_complete_original_word_source_sqrt_derives_original_input_square_without_inverse_correctness
    (input returned : CanonicalScalar) (actualInverse : Vector UInt64 4)
    (success : sourceWordSqrt input actualInverse = some returned) :
    sourceBlstFrWordMeaning returned.words^2 = sourceBlstFrWordMeaning input.words := by
  unfold sourceWordSqrt at success
  split at success
  next zero =>
    have same := Option.some.inj success
    subst returned
    simp only [zero,original_caller_zero_has_the_exact_zero_field_meaning,zero_pow (by decide : 2 ≠ 0)]
  next nonzero =>
    have budget := original_bounded_word_loop_agrees_with_actual_decreasing_word_while input 32
      (sourceWordInitial input actualInverse) (by change 1 ≤ 32; decide) (by change 32 ≤ 32; decide)
    exact returned_original_word_loop_derives_original_input_square input returned 32
      (sourceWordInitial input actualInverse) (budget.trans success)
set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @WordState
#print axioms WordState
set_option pp.all true in
#check @sourceWordUpdate
#print axioms sourceWordUpdate
set_option pp.all true in
#check @sourceCheckedRoot
#print axioms sourceCheckedRoot
set_option pp.all true in
#check @returned_original_word_final_check_derives_original_input_square
#print axioms returned_original_word_final_check_derives_original_input_square
set_option pp.all true in
#check @sourceWordLoop
#print axioms sourceWordLoop
set_option pp.all true in
#check @returned_original_word_loop_derives_original_input_square
#print axioms returned_original_word_loop_derives_original_input_square
set_option pp.all true in
#check @sourceWordWhile
#print axioms sourceWordWhile
set_option pp.all true in
#check @original_bounded_word_loop_agrees_with_actual_decreasing_word_while
#print axioms original_bounded_word_loop_agrees_with_actual_decreasing_word_while
set_option pp.all true in
#check @sourceCallerRoot
#print axioms sourceCallerRoot
set_option pp.all true in
#check @sourceCallerZero
#print axioms sourceCallerZero
set_option pp.all true in
#check @original_caller_zero_has_the_exact_zero_field_meaning
#print axioms original_caller_zero_has_the_exact_zero_field_meaning
set_option pp.all true in
#check @sourceWordInitial
#print axioms sourceWordInitial
set_option pp.all true in
#check @sourceWordSqrt
#print axioms sourceWordSqrt
set_option pp.all true in
#check @returned_complete_original_word_source_sqrt_derives_original_input_square_without_inverse_correctness
#print axioms returned_complete_original_word_source_sqrt_derives_original_input_square_without_inverse_correctness
end ShielddSecurity.TransferBlstArmSqrtWhile01
