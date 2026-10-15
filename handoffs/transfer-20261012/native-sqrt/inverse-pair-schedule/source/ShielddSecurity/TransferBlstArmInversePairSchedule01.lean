import ShielddSecurity.TransferBlstArmInverseWindowGcd01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePairSchedule01
open TransferBlstArmInverseBitlengthBudget01 (sourceNatBitlength)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)

/-! Symbolic recurrence over an abstract pair step. The source application
must establish every contract field from its actual batch lemmas; none is
native correspondence or a free premise of the final source endpoint. -/

structure PairStepContract (step : Nat × Nat → Nat × Nat) : Prop where
  odd : ∀ input, input.2 % 2 = 1 → (step input).2 % 2 = 1
  capacity : ∀ input, input.2 % 2 = 1 → (step input).1 < 2 ^ 256 ∧ (step input).2 < 2 ^ 256
  zero : ∀ input, input.1 = 0 → (step input).1 = 0
  progress : ∀ input, input.1 < 2 ^ 256 → input.2 < 2 ^ 256 → input.2 % 2 = 1 →
    (step input).1 = 0 ∨ sourceNatBitlength (step input).1 + sourceNatBitlength (step input).2 + 31 ≤
      sourceNatBitlength input.1 + sourceNatBitlength input.2

def symbolicPairSchedule (step : Nat × Nat → Nat × Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, input => input
  | count + 1, input => symbolicPairSchedule step count (step input)

theorem plain_size_decreases_compose
    (initial next final count : Nat) (first : next + 31 ≤ initial)
    (suffix : final + 31 * count ≤ next) : final + 31 * (count + 1) ≤ initial := by omega

theorem plain_size_decrease_leaves_the_tail_budget
    (initial final count tail : Nat) (progress : final + 31 * count ≤ initial)
    (budget : initial ≤ 31 * count + tail) : final ≤ tail := by omega

theorem symbolic_schedule_retains_odd_second_value
    (step : Nat × Nat → Nat × Nat) (contract : PairStepContract step)
    (count : Nat) (input : Nat × Nat) (odd : input.2 % 2 = 1) :
    (symbolicPairSchedule step count input).2 % 2 = 1 := by
  induction count generalizing input with
  | zero => exact odd
  | succ count ih => exact ih (step input) (contract.odd input odd)

theorem symbolic_schedule_retains_capacity
    (step : Nat × Nat → Nat × Nat) (contract : PairStepContract step)
    (count : Nat) (input : Nat × Nat) (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256)
    (odd : input.2 % 2 = 1) :
    (symbolicPairSchedule step count input).1 < 2 ^ 256 ∧ (symbolicPairSchedule step count input).2 < 2 ^ 256 := by
  induction count generalizing input with
  | zero => exact ⟨leftBound, rightBound⟩
  | succ count ih =>
    have next := contract.capacity input odd
    exact ih (step input) next.1 next.2 (contract.odd input odd)

theorem symbolic_schedule_retains_zero_first_value
    (step : Nat × Nat → Nat × Nat) (contract : PairStepContract step)
    (count : Nat) (input : Nat × Nat) (zero : input.1 = 0) :
    (symbolicPairSchedule step count input).1 = 0 := by
  induction count generalizing input with
  | zero => exact zero
  | succ count ih => exact ih (step input) (contract.zero input zero)

theorem symbolic_schedule_reaches_zero_or_decreases_size_by31_per_step
    (step : Nat × Nat → Nat × Nat) (contract : PairStepContract step)
    (count : Nat) (input : Nat × Nat) (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256)
    (odd : input.2 % 2 = 1) :
    (symbolicPairSchedule step count input).1 = 0 ∨
      sourceNatBitlength (symbolicPairSchedule step count input).1 +
        sourceNatBitlength (symbolicPairSchedule step count input).2 + 31 * count ≤
          sourceNatBitlength input.1 + sourceNatBitlength input.2 := by
  induction count generalizing input with
  | zero => right; exact Nat.le_refl _
  | succ count ih =>
    have next := contract.capacity input odd
    have suffix := ih (step input) next.1 next.2 (contract.odd input odd)
    rcases suffix with terminal | decrease
    · left; exact terminal
    · rcases contract.progress input leftBound rightBound odd with firstZero | firstDecrease
      · left
        exact symbolic_schedule_retains_zero_first_value step contract count (step input) firstZero
      · right
        exact plain_size_decreases_compose _ _ _ count firstDecrease decrease

theorem symbolic_schedule_reaches_zero_or_leaves_the_tail_size_budget
    (step : Nat × Nat → Nat × Nat) (contract : PairStepContract step)
    (count tail : Nat) (input : Nat × Nat)
    (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256) (odd : input.2 % 2 = 1)
    (budget : sourceNatBitlength input.1 + sourceNatBitlength input.2 ≤ 31 * count + tail) :
    (symbolicPairSchedule step count input).1 = 0 ∨
      sourceNatBitlength (symbolicPairSchedule step count input).1 +
        sourceNatBitlength (symbolicPairSchedule step count input).2 ≤ tail := by
  have progress := symbolic_schedule_reaches_zero_or_decreases_size_by31_per_step step contract count input leftBound rightBound odd
  rcases progress with terminal | decrease
  · left; exact terminal
  · right; exact plain_size_decrease_leaves_the_tail_budget _ _ count tail decrease budget

theorem symbolic_schedule_and_a_sufficient_exact_natural_tail_reach_zero
    (step : Nat × Nat → Nat × Nat) (contract : PairStepContract step)
    (count tail : Nat) (input : Nat × Nat)
    (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256) (odd : input.2 % 2 = 1)
    (budget : sourceNatBitlength input.1 + sourceNatBitlength input.2 ≤ 31 * count + tail) :
    (sourceFactorWalk tail (sourceFactorInitial
      (symbolicPairSchedule step count input).1 (symbolicPairSchedule step count input).2)).a = 0 := by
  have cases := symbolic_schedule_reaches_zero_or_leaves_the_tail_size_budget step contract count tail input leftBound rightBound odd budget
  rcases cases with terminal | small
  · exact TransferBlstArmInverseNaturalProgress01.a_zero_first_natural_component_stays_zero_for_every_factor_walk
      tail (sourceFactorInitial (symbolicPairSchedule step count input).1 (symbolicPairSchedule step count input).2) terminal
  · exact TransferBlstArmInverseNaturalTermination01.an_odd_second_input_and_enough_exact_steps_force_a_zero_first_output
      tail (sourceFactorInitial (symbolicPairSchedule step count input).1 (symbolicPairSchedule step count input).2)
      (symbolic_schedule_retains_odd_second_value step contract count input odd) small

set_option pp.all true in
#check @PairStepContract
#print axioms PairStepContract
set_option pp.all true in
#check @symbolicPairSchedule
#print axioms symbolicPairSchedule
set_option pp.all true in
#check @plain_size_decreases_compose
#print axioms plain_size_decreases_compose
set_option pp.all true in
#check @plain_size_decrease_leaves_the_tail_budget
#print axioms plain_size_decrease_leaves_the_tail_budget
set_option pp.all true in
#check @symbolic_schedule_retains_odd_second_value
#print axioms symbolic_schedule_retains_odd_second_value
set_option pp.all true in
#check @symbolic_schedule_retains_capacity
#print axioms symbolic_schedule_retains_capacity
set_option pp.all true in
#check @symbolic_schedule_retains_zero_first_value
#print axioms symbolic_schedule_retains_zero_first_value
set_option pp.all true in
#check @symbolic_schedule_reaches_zero_or_decreases_size_by31_per_step
#print axioms symbolic_schedule_reaches_zero_or_decreases_size_by31_per_step
set_option pp.all true in
#check @symbolic_schedule_reaches_zero_or_leaves_the_tail_size_budget
#print axioms symbolic_schedule_reaches_zero_or_leaves_the_tail_size_budget
set_option pp.all true in
#check @symbolic_schedule_and_a_sufficient_exact_natural_tail_reach_zero
#print axioms symbolic_schedule_and_a_sufficient_exact_natural_tail_reach_zero
end ShielddSecurity.TransferBlstArmInversePairSchedule01
