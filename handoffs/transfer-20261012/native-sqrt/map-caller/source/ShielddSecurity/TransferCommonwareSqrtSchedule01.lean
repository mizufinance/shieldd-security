import ShielddSecurity.TransferCommonwareSqrtComplete01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCommonwareSqrtSchedule01
open FfFinishedPhase296 (State)
open TransferCommonwareSqrtSearch01
open TransferCommonwareSqrtLoop01
open TransferCommonwareSqrtComplete01
open TransferFfFieldApi01
open TransferBoundedNativeCodec01 (nullifierModulus)
variable {F : Type} [Field F] [DecidableEq F]

theorem every_successful_search_walk_returns_an_index_inside_the_actual_schedule
    (m fuel i k : Nat) (value : F) (inside : i < m) (success : searchWalk m fuel i value = some k) :
    i ≤ k ∧ k < m := by
  induction fuel generalizing i value with
  | zero => simp only [searchWalk,reduceCtorEq] at success
  | succ fuel ih =>
    by_cases unit : value=1
    · simp only [searchWalk,if_pos unit,Option.some.injEq] at success
      subst k
      exact ⟨Nat.le_refl _,inside⟩
    · by_cases boundary : i+1=m
      · simp only [searchWalk,if_neg unit,if_pos boundary,reduceCtorEq] at success
      · rw [searchWalk,if_neg unit,if_neg boundary] at success
        obtain ⟨lower,upper⟩ := ih (i+1) (value*value) (by omega) success
        exact ⟨by omega,upper⟩

theorem every_successful_source_search_returns_an_index_below_m (m k : Nat) (value : F)
    (success : sourceSearch m value = some k) : k < m := by
  by_cases positive : 0 < m
  · exact (every_successful_search_walk_returns_an_index_inside_the_actual_schedule m m 0 k value positive success).2
  · have zero : m=0 := by omega
    simp only [sourceSearch,zero,searchWalk,reduceCtorEq] at success

theorem every_successful_nonunit_source_search_returns_a_positive_index (m k : Nat) (value : F)
    (nonunit : value ≠ 1) (success : sourceSearch m value = some k) : 1 ≤ k := by
  cases m with
  | zero => simp only [sourceSearch,searchWalk,reduceCtorEq] at success
  | succ m =>
    unfold sourceSearch at success
    rw [searchWalk,if_neg nonunit] at success
    by_cases boundary : 0+1 = m+1
    · simp only [if_pos boundary,reduceCtorEq] at success
    · rw [if_neg boundary] at success
      exact (every_successful_search_walk_returns_an_index_inside_the_actual_schedule
        (m+1) m 1 k (value*value) (by omega) success).1

/-- The distinct source while loop has no supplied traversal budget. Termination
uses the bound proved from its actual successful inner search, for all inputs. -/
def sourceWhile (input : F) (s : State F) : Option F :=
  if s.b = 1 then if s.x*s.x = input then some s.x else none
  else match _found : sourceSearch s.v s.b with
    | none => none
    | some i => sourceWhile input (sourceUpdate s i)
termination_by s.v
decreasing_by
  exact every_successful_source_search_returns_an_index_below_m s.v i s.b _found

theorem actual_budgeted_loop_agrees_with_the_well_founded_source_while
    (input : F) (fuel : Nat) (s : State F) (positive : 1 ≤ s.v) (bounded : s.v ≤ fuel) :
    sourceLoop input fuel s = sourceWhile input s := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    rw [sourceLoop,sourceWhile]
    by_cases unit : s.b=1
    · simp only [if_pos unit]
    · simp only [if_neg unit]
      cases found : sourceSearch s.v s.b with
      | none => simp only [Option.bind_none]
      | some i =>
        simp only [Option.bind_some]
        have lower := every_successful_nonunit_source_search_returns_a_positive_index s.v i s.b unit found
        have upper := every_successful_source_search_returns_an_index_below_m s.v i s.b found
        exact ih (sourceUpdate s i) lower (by change i ≤ fuel; omega)

local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

def sourceCommonwareWhileSqrt (input : ZMod nullifierModulus) : Option (ZMod nullifierModulus) :=
  if input=0 then some 0 else sourceWhile input (sourceInitial (fieldScalar input))

theorem actual_commonware_while_and_budgeted_producers_agree_on_every_input (input : ZMod nullifierModulus) :
    sourceCommonwareWhileSqrt input = sourceCommonwareFieldSqrt input := by
  unfold sourceCommonwareWhileSqrt sourceCommonwareFieldSqrt
  split
  · rfl
  · rw [actual_budgeted_loop_agrees_with_the_well_founded_source_while input 32
      (sourceInitial (fieldScalar input)) (by change 1 ≤ 32; decide) (by change 32 ≤ 32; decide)]

theorem actual_commonware_source_while_has_the_total_square_contract (input : ZMod nullifierModulus) :
    (sourceCommonwareWhileSqrt input).isSome = true ↔ IsSquare input := by
  rw [actual_commonware_while_and_budgeted_producers_agree_on_every_input]
  exact actual_commonware_source_field_sqrt_has_the_total_square_contract input


theorem every_actual_commonware_search_increment_fits_the_unsigned_word
    (m j : Nat) (inside : j < m) (bounded : m ≤ 32) :
    ((UInt32.ofNat j)+1).toNat = j+1 := by
  have wordSize : UInt32.size = 4294967296 := rfl
  have indexBound : j < UInt32.size := by rw [wordSize]; omega
  rw [UInt32.toNat_add,UInt32.toNat_ofNat_of_lt' indexBound]
  have one : (1 : UInt32).toNat = 1 := rfl
  rw [one]
  exact Nat.mod_eq_of_lt (by omega)

set_option pp.all true in
#check @every_successful_search_walk_returns_an_index_inside_the_actual_schedule
#print axioms every_successful_search_walk_returns_an_index_inside_the_actual_schedule
set_option pp.all true in
#check @every_successful_source_search_returns_an_index_below_m
#print axioms every_successful_source_search_returns_an_index_below_m
set_option pp.all true in
#check @every_successful_nonunit_source_search_returns_a_positive_index
#print axioms every_successful_nonunit_source_search_returns_a_positive_index
set_option pp.all true in
#check @sourceWhile
#print axioms sourceWhile
set_option pp.all true in
#check @actual_budgeted_loop_agrees_with_the_well_founded_source_while
#print axioms actual_budgeted_loop_agrees_with_the_well_founded_source_while
set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @sourceCommonwareWhileSqrt
#print axioms sourceCommonwareWhileSqrt
set_option pp.all true in
#check @actual_commonware_while_and_budgeted_producers_agree_on_every_input
#print axioms actual_commonware_while_and_budgeted_producers_agree_on_every_input
set_option pp.all true in
#check @actual_commonware_source_while_has_the_total_square_contract
#print axioms actual_commonware_source_while_has_the_total_square_contract
set_option pp.all true in
#check @every_actual_commonware_search_increment_fits_the_unsigned_word
#print axioms every_actual_commonware_search_increment_fits_the_unsigned_word
end ShielddSecurity.TransferCommonwareSqrtSchedule01
