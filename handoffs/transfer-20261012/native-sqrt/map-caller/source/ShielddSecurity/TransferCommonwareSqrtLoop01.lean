import ShielddSecurity.TransferCommonwareSqrtSearch01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCommonwareSqrtLoop01
open FfFinishedPhase296 (State)
open TransferCommonwareSqrtSearch01
open TransferFfLeastPower01
open TransferFfActiveAlgebra01
variable {F : Type} [Field F] [DecidableEq F]

def Good (input : F) (s : State F) : Prop :=
  1 ≤ s.v ∧ s.x ^ 2 = input * s.b ∧ s.b ^ (2^(s.v-1)) = 1 ∧
    s.z ^ (2^s.v) = 1 ∧ s.z ^ (2^(s.v-1)) = -1

def sourceUpdate (s : State F) (i : Nat) : State F :=
  let b := squareWalk (s.v-i-1) s.z
  let c := b*b
  ⟨s.x*b,s.b*c,c,i⟩

def sourceLoop (input : F) : Nat → State F → Option F
  | 0,_ => none
  | fuel+1,s =>
    if s.b = 1 then if s.x*s.x = input then some s.x else none
    else (sourceSearch s.v s.b).bind fun i => sourceLoop input fuel (sourceUpdate s i)

theorem every_commonware_loop_success_has_the_checked_root
    (input : F) (fuel : Nat) (s : State F) (returned : F)
    (success : sourceLoop input fuel s = some returned) : returned*returned = input := by
  induction fuel generalizing s with
  | zero => simp [sourceLoop] at success
  | succ fuel ih =>
    by_cases unit : s.b = 1
    · rw [sourceLoop,if_pos unit] at success
      by_cases checked : s.x*s.x = input
      · rw [if_pos checked] at success
        cases Option.some.inj success
        exact checked
      · simp only [if_neg checked,reduceCtorEq] at success
    · rw [sourceLoop,if_neg unit] at success
      cases search : sourceSearch s.v s.b with
      | none => simp only [search,Option.bind_none,reduceCtorEq] at success
      | some i => exact ih (sourceUpdate s i) (by simpa only [search,Option.bind_some] using success)

theorem actual_commonware_nonunit_update_derives_a_smaller_good_state
    (input : F) (s : State F) (good : Good input s) (nonunit : s.b ≠ 1) :
    let active : 1 < s.v := by
      have positive := good.1
      have bound := good.2.2.1
      by_contra absent
      have one : s.v=1 := by omega
      exact nonunit (by simpa only [one,Nat.sub_self,pow_zero,pow_one] using bound)
    let k := leastPositiveExponent s.b s.v active good.2.2.1
    sourceSearch s.v s.b = some k ∧ Good input (sourceUpdate s k) ∧ (sourceUpdate s k).v < s.v := by
  dsimp only
  have active : 1 < s.v := by
    have positive := good.1
    have bound := good.2.2.1
    by_contra absent
    have one : s.v=1 := by omega
    exact nonunit (by simpa only [one,Nat.sub_self,pow_zero,pow_one] using bound)
  let k := leastPositiveExponent s.b s.v active good.2.2.1
  change sourceSearch s.v s.b = some k ∧ Good input (sourceUpdate s k) ∧ (sourceUpdate s k).v < s.v
  have spec : 1 ≤ k ∧ k < s.v ∧ s.b ^ (2^k) = 1 :=
    derived_least_positive_exponent_has_exact_search_bounds_and_power s.b s.v active good.2.2.1
  have previous : s.b ^ (2^(k-1)) ≠ 1 := by
    by_cases first : k = 1
    · simpa only [first,Nat.sub_self,pow_zero,pow_one] using nonunit
    · exact every_earlier_positive_power_before_the_derived_index_is_not_one
        s.b s.v active good.2.2.1 (k-1) (by omega) (by omega)
  have correctionMatch : squareWalk (s.v-k-1) s.z = correction s.z s.v k :=
    actual_commonware_correction_walk_has_the_exact_power _ _
  refine ⟨actual_commonware_search_derives_the_least_positive_exponent s.b s.v active good.2.2.1 nonunit,?_,spec.2.1⟩
  simp only [Good,sourceUpdate,correctionMatch,← pow_two]
  exact ⟨spec.1,active_candidate_update_preserves_exact_residue_tracking _ _ _ _ good.2.1,
    active_residue_update_derives_a_strictly_smaller_half_order_bound _ _ _ _ spec.1 spec.2.1 spec.2.2 previous good.2.2.2.2,
    active_correction_square_has_reduced_full_power _ _ _ spec.2.1 good.2.2.2.1,
    active_correction_square_has_reduced_negative_half_power _ _ _ spec.1 spec.2.1 good.2.2.2.2⟩

theorem actual_commonware_loop_is_complete_from_derived_good_invariants
    (input : F) (fuel : Nat) (s : State F) (good : Good input s) (bounded : s.v ≤ fuel) :
    ∃ returned, sourceLoop input fuel s = some returned := by
  induction fuel generalizing s with
  | zero => have := good.1; omega
  | succ fuel ih =>
    by_cases unit : s.b = 1
    · have checked : s.x*s.x = input := by simpa only [unit,mul_one,pow_two] using good.2.1
      exact ⟨s.x,by simp only [sourceLoop,if_pos unit,if_pos checked]⟩
    · obtain ⟨found,nextGood,smaller⟩ := actual_commonware_nonunit_update_derives_a_smaller_good_state input s good unit
      obtain ⟨returned,success⟩ := ih _ nextGood (by omega)
      exact ⟨returned,by simpa only [sourceLoop,if_neg unit,found,Option.bind_some] using success⟩

set_option pp.all true in
#check @Good
#print axioms Good
set_option pp.all true in
#check @sourceUpdate
#print axioms sourceUpdate
set_option pp.all true in
#check @sourceLoop
#print axioms sourceLoop
set_option pp.all true in
#check @every_commonware_loop_success_has_the_checked_root
#print axioms every_commonware_loop_success_has_the_checked_root
set_option pp.all true in
#check @actual_commonware_nonunit_update_derives_a_smaller_good_state
#print axioms actual_commonware_nonunit_update_derives_a_smaller_good_state
set_option pp.all true in
#check @actual_commonware_loop_is_complete_from_derived_good_invariants
#print axioms actual_commonware_loop_is_complete_from_derived_good_invariants
end ShielddSecurity.TransferCommonwareSqrtLoop01
