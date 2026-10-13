import ShielddSecurity.FfFinishedPhase296
import ShielddSecurity.TransferFfLeastPower01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferFfActiveScan01
open FfFinishedPhase296 (Inner innerStep)
variable {F : Type} [Field F]
/-! Symbolic prefix phases for the exact mathematical ff inner recurrence.
The positive index/powers are derived by leastPositiveExponent, and the
actual native-word loop must be joined by field/unsigned-value projection. -/

def phaseState (b z : F) (k v next : Nat) : Inner F :=
  if next ≤ k + 1 then ⟨next - 1, b ^ (2 ^ (next - 1)), z, true⟩
  else ⟨k, 1, z ^ (2 ^ (min next v - k - 1)), decide (next ≤ v)⟩

theorem next_repeated_square_power (base : F) (j : Nat) (positive : 1 ≤ j) :
    base ^ (2 ^ (j - 1)) * base ^ (2 ^ (j - 1)) = base ^ (2 ^ j) := by
  rw [← pow_two, ← pow_mul, ← Nat.pow_succ, Nat.succ_eq_add_one]
  have count : j - 1 + 1 = j := by omega
  rw [count]

theorem phase_state_at_initial_index (b z : F) (k v : Nat) (positive : 1 ≤ k) :
    phaseState b z k v 2 = ⟨1,b*b,z,true⟩ := by
  simp [phaseState, show 2 ≤ k+1 by omega, pow_two]

variable [DecidableEq F]
theorem exact_inner_step_advances_the_symbolic_phase
    (b z : F) (k v j : Nat) (smaller : k < v) (lower : 2 ≤ j)
    (power : b ^ (2 ^ k) = 1)
    (earlier : ∀ i : Nat, 1 ≤ i → i < k → b ^ (2 ^ i) ≠ 1) :
    innerStep v (phaseState b z k v j) j = phaseState b z k v (j+1) := by
  by_cases before : j ≤ k + 1
  · by_cases advancing : j ≤ k
    · have nonOne := earlier (j-1) (by omega) (by omega)
      have different : j ≠ v := by omega
      have nextBefore : j+1 ≤ k+1 := by omega
      have squared := next_repeated_square_power b j (by omega)
      simp [phaseState, before, nextBefore, innerStep, nonOne, different, squared]
    · have threshold : j = k+1 := by omega
      subst j
      have oldPhase : phaseState b z k v (k+1) = ⟨k,b^(2^k),z,true⟩ := by
        simp [phaseState]
      rw [oldPhase]
      have nextAfter : ¬ k+1+1 ≤ k+1 := by omega
      by_cases boundary : k+1 = v
      · have minimum : min (k+1+1) v = v := min_eq_right (by omega)
        have count : v-k-1 = 0 := by omega
        have below : ¬ k+1+1 ≤ v := by omega
        simp only [phaseState, if_neg nextAfter, minimum, count, pow_zero, pow_one]
        simp [innerStep, power, ← boundary]
      · have minimum : min (k+1+1) v = k+1+1 := min_eq_left (by omega)
        have count : k+1+1-k-1 = 1 := by omega
        have below : k+1+1 ≤ v := by omega
        simp [phaseState, nextAfter, innerStep, power, boundary, count, below, pow_two]
  · have nextAfter : ¬ j+1 ≤ k+1 := by omega
    by_cases stillBelow : j < v
    · have oldBelow : j ≤ v := by omega
      have newBelow : j+1 ≤ v := by omega
      have different : j ≠ v := by omega
      have minimum : min j v = j := min_eq_left oldBelow
      have nextMinimum : min (j+1) v = j+1 := min_eq_left newBelow
      have previousPositive : 1 ≤ j-k := by omega
      have previousCount : j-k-1 = (j-k)-1 := rfl
      have nextCount : j+1-k-1 = j-k := by omega
      have squared := next_repeated_square_power z (j-k) previousPositive
      simp [phaseState, before, nextAfter, innerStep, oldBelow, newBelow, different,
        nextCount, squared]
    · have minimum : min j v = v := min_eq_right (by omega)
      have nextMinimum : min (j+1) v = v := min_eq_right (by omega)
      have newBelow : ¬ j+1 ≤ v := by omega
      by_cases boundary : j = v
      · subst j
        simp [phaseState, before, nextAfter, innerStep, newBelow]
      · have oldBelow : ¬ j ≤ v := by omega
        simp [phaseState, before, nextAfter, innerStep, minimum, nextMinimum, oldBelow, newBelow]


theorem exact_inner_prefix_fold_has_the_symbolic_phase
    (b z : F) (k v start count : Nat) (smaller : k < v)
    (lower : 2 ≤ start) (power : b ^ (2 ^ k) = 1)
    (earlier : ∀ i : Nat, 1 ≤ i → i < k → b ^ (2 ^ i) ≠ 1) :
    (List.range' start count).foldl (innerStep v) (phaseState b z k v start) =
      phaseState b z k v (start+count) := by
  induction count generalizing start with
  | zero => simp
  | succ count ih =>
    simp only [List.range'_succ, List.foldl_cons]
    rw [exact_inner_step_advances_the_symbolic_phase b z k v start smaller lower power earlier]
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using
      ih (start+1) (by omega)

theorem actual_inner_scan_derives_least_index_and_correction
    (s : FfFinishedPhase296.State F) (maxV : Nat) (active : 1 < s.v)
    (schedule : s.v ≤ maxV) (bound : s.b ^ (2 ^ (s.v-1)) = 1) :
    let k := TransferFfLeastPower01.leastPositiveExponent s.b s.v active bound
    (FfFinishedPhase296.innerFor maxV s).k = k ∧
    (FfFinishedPhase296.innerFor maxV s).b2k = 1 ∧
    (FfFinishedPhase296.innerFor maxV s).z = s.z ^ (2 ^ (s.v-k-1)) := by
  dsimp only
  let k := TransferFfLeastPower01.leastPositiveExponent s.b s.v active bound
  change (FfFinishedPhase296.innerFor maxV s).k = k ∧
    (FfFinishedPhase296.innerFor maxV s).b2k = 1 ∧
    (FfFinishedPhase296.innerFor maxV s).z = s.z ^ (2 ^ (s.v-k-1))
  have spec : 1 ≤ k ∧ k < s.v ∧ s.b ^ (2^k) = 1 := TransferFfLeastPower01.derived_least_positive_exponent_has_exact_search_bounds_and_power
    s.b s.v active bound
  have earlier := TransferFfLeastPower01.every_earlier_positive_power_before_the_derived_index_is_not_one
    s.b s.v active bound
  have initial := phase_state_at_initial_index s.b s.z k s.v spec.1
  have folded := exact_inner_prefix_fold_has_the_symbolic_phase s.b s.z k s.v 2 (maxV-2)
    spec.2.1 (by decide) spec.2.2 earlier
  have count : 2+(maxV-2) = maxV := by omega
  rw [initial, count] at folded
  change FfFinishedPhase296.innerFor maxV s = phaseState s.b s.z k s.v maxV at folded
  rw [folded]
  by_cases boundary : maxV ≤ k+1
  · have equal : maxV = k+1 := by omega
    have equalV : maxV = s.v := by omega
    have countZero : s.v-k-1=0 := by omega
    simp [phaseState, equal, spec.2.2, countZero]
  · simp [phaseState, boundary, min_eq_right schedule]

set_option pp.all true in
#check @phaseState
#print axioms phaseState
set_option pp.all true in
#check @next_repeated_square_power
#print axioms next_repeated_square_power
set_option pp.all true in
#check @phase_state_at_initial_index
#print axioms phase_state_at_initial_index
set_option pp.all true in
#check @exact_inner_step_advances_the_symbolic_phase
#print axioms exact_inner_step_advances_the_symbolic_phase
set_option pp.all true in
#check @exact_inner_prefix_fold_has_the_symbolic_phase
#print axioms exact_inner_prefix_fold_has_the_symbolic_phase
set_option pp.all true in
#check @actual_inner_scan_derives_least_index_and_correction
#print axioms actual_inner_scan_derives_least_index_and_correction
end ShielddSecurity.TransferFfActiveScan01
