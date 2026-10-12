import ShielddSecurity.TransferFfActiveScan01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferFfActiveCompleteness01
open FfFinishedPhase296
open TransferFfLeastPower01
open TransferFfActiveAlgebra01
variable {F : Type} [Field F] [DecidableEq F]

def Active (input : F) (s : State F) : Prop :=
  1 < s.v ∧ s.x ^ 2 = input * s.b ∧ s.b ^ (2 ^ (s.v-1)) = 1 ∧
    s.z ^ (2 ^ s.v) = 1 ∧ s.z ^ (2 ^ (s.v-1)) = -1

def Ready (input : F) (limit : Nat) (s : State F) : Prop :=
  Finished input s ∨ Active input s ∧ s.v ≤ limit

theorem unit_residue_has_least_positive_index_one (b : F) (v : Nat)
    (active : 1 < v) (bound : b ^ (2 ^ (v-1)) = 1) (unit : b = 1) :
    leastPositiveExponent b v active bound = 1 := by
  have spec := derived_least_positive_exponent_has_exact_search_bounds_and_power b v active bound
  by_contra different
  have earlier := every_earlier_positive_power_before_the_derived_index_is_not_one
    b v active bound 1 (by decide) (by omega)
  exact earlier (by simp [unit])

theorem actual_active_outer_step_reduces_the_schedule_or_finishes
    (input : F) (maxV : Nat) (s : State F) (active : Active input s) (schedule : s.v ≤ maxV) :
    Ready input (maxV-1) (outerStep maxV s) := by
  obtain ⟨larger,tracking,bound,full,half⟩ := active
  let k := leastPositiveExponent s.b s.v larger bound
  have spec : 1 ≤ k ∧ k < s.v ∧ s.b ^ (2^k) = 1 :=
    derived_least_positive_exponent_has_exact_search_bounds_and_power s.b s.v larger bound
  have scan := TransferFfActiveScan01.actual_inner_scan_derives_least_index_and_correction s maxV larger schedule bound
  have update : outerStep maxV s =
      ⟨if s.b = 1 then s.x else s.x * correction s.z s.v k,
        s.b * correction s.z s.v k ^ 2, correction s.z s.v k ^ 2, k⟩ := by
    simp [outerStep, scan.1, scan.2.2, correction, k, pow_two]
  rw [update]
  by_cases unit : s.b = 1
  · have first : k = 1 := unit_residue_has_least_positive_index_one s.b s.v larger bound unit
    obtain ⟨root,newB,newZ⟩ := active_unit_residue_update_derives_the_finished_state input s.x s.b s.z s.v
      larger tracking unit half
    left
    simp only [Finished, if_pos unit, first]
    exact ⟨by simpa only [pow_two] using root, True.intro,
      by simpa only [pow_two] using newB, by simpa only [pow_two] using newZ⟩
  · have previous : s.b ^ (2^(k-1)) ≠ 1 := by
      by_cases first : k = 1
      · simpa only [first,Nat.sub_self,pow_zero,pow_one] using unit
      · exact every_earlier_positive_power_before_the_derived_index_is_not_one
          s.b s.v larger bound (k-1) (by omega) (by omega)
    have newBound := active_residue_update_derives_a_strictly_smaller_half_order_bound
      s.b s.z s.v k spec.1 spec.2.1 spec.2.2 previous half
    have newTracking := active_candidate_update_preserves_exact_residue_tracking
      input s.x s.b (correction s.z s.v k) tracking
    have newFull := active_correction_square_has_reduced_full_power s.z s.v k spec.2.1 full
    have newHalf := active_correction_square_has_reduced_negative_half_power s.z s.v k spec.1 spec.2.1 half
    by_cases first : k = 1
    · left
      have newB : s.b * correction s.z s.v k ^ 2 = 1 := by
        simpa only [first,Nat.sub_self,pow_zero,pow_one] using newBound
      have newZ : (correction s.z s.v k ^ 2) ^ 2 = 1 := by
        simpa only [first,pow_one] using newFull
      refine ⟨?_,first,?_,?_⟩
      · rw [newB,mul_one] at newTracking
        simpa only [if_neg unit,pow_two] using newTracking
      · simp only [newB,one_mul]
      · simpa only [pow_two] using newZ
    · right
      refine ⟨⟨?_,?_,newBound,newFull,newHalf⟩,?_⟩
      · change 1 < k
        omega
      · simpa only [if_neg unit] using newTracking
      · change k ≤ maxV-1
        omega

def descendingRounds (count : Nat) : List Nat := (List.range count).reverse.map (·+1)

theorem descending_rounds_successor (count : Nat) :
    descendingRounds (count+1) = (count+1) :: descendingRounds count := by
  simp [descendingRounds,List.range_succ,List.reverse_append]

theorem exact_descending_outer_loop_finishes_every_ready_state
    (input : F) (count : Nat) (s : State F) (ready : Ready input count s) :
    Finished input (outerLoop (descendingRounds count) s) := by
  induction count generalizing s with
  | zero =>
    rcases ready with finished | ⟨active,bounded⟩
    · simpa only [descendingRounds,List.range_zero,List.reverse_nil,List.map_nil,outerLoop,List.foldl_nil] using finished
    · have := active.1
      omega
  | succ count ih =>
    rw [descending_rounds_successor]
    change Finished input (outerLoop (descendingRounds count) (outerStep (count+1) s))
    apply ih
    rcases ready with finished | ⟨active,bounded⟩
    · exact Or.inl (outer_finished input (count+1) s finished)
    · simpa only [Nat.add_sub_cancel] using
        actual_active_outer_step_reduces_the_schedule_or_finishes input (count+1) s active bounded

set_option pp.all true in
#check @Active
#print axioms Active
set_option pp.all true in
#check @Ready
#print axioms Ready
set_option pp.all true in
#check @unit_residue_has_least_positive_index_one
#print axioms unit_residue_has_least_positive_index_one
set_option pp.all true in
#check @actual_active_outer_step_reduces_the_schedule_or_finishes
#print axioms actual_active_outer_step_reduces_the_schedule_or_finishes
set_option pp.all true in
#check @descendingRounds
#print axioms descendingRounds
set_option pp.all true in
#check @descending_rounds_successor
#print axioms descending_rounds_successor
set_option pp.all true in
#check @exact_descending_outer_loop_finishes_every_ready_state
#print axioms exact_descending_outer_loop_finishes_every_ready_state
end ShielddSecurity.TransferFfActiveCompleteness01
