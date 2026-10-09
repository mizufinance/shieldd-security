import ShielddSecurity.TransferReducedKeyCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferReducedKeyQueries

open scoped BigOperators
open TransferReducedKeyCounting

local instance : IsOrderedAddMonoid ℚ where
  add_le_add_left := fun _ _ inequality _ => Rat.add_le_add_right.2 inequality

local instance : IsStrictOrderedRing ℚ := .of_mul_pos fun _ _ positiveLeft positiveRight ↦
  (Rat.mul_nonneg positiveLeft.le positiveRight.le).lt_of_ne'
    (mul_ne_zero positiveLeft.ne' positiveRight.ne')

abbrev NonzeroFiber (scalar : Nat) :=
  {value : NonzeroOutput // value.val.val % Scalar.order = scalar}

def forgetNonzero (scalar : Nat) (value : NonzeroFiber scalar) : Fiber scalar :=
  ⟨value.val.val,value.property⟩

theorem nonzero_fiber_card_le_nine (scalar : Nat) :
    Fintype.card (NonzeroFiber scalar) ≤ 9 := by
  have injective : Function.Injective (forgetNonzero scalar) := by
    intro first second same
    have underlying : first.val.val = second.val.val :=
      congrArg (fun value : Fiber scalar => value.val) same
    exact Subtype.ext (Subtype.ext underlying)
  exact (Fintype.card_le_of_injective (forgetNonzero scalar) injective).trans
    (fiber_card_le_nine scalar)

/-- Exact uniform sampling after the SDK rejects zero reduced outputs. This
models conditioning a fresh uniform canonical field answer, not a security
property of the concrete Poseidon implementation or of arbitrary hash inputs. -/
def conditionalHitFraction (scalar : Nat) : ℚ :=
  (Fintype.card (NonzeroFiber scalar) : ℚ) / (Fintype.card NonzeroOutput : ℚ)

def bound : ℚ := 9 / ((Scalar.modulus - 9 : Nat) : ℚ)

theorem conditional_hit_bound (scalar : Nat) : conditionalHitFraction scalar ≤ bound := by
  rw [conditionalHitFraction,nonzero_output_card]
  exact div_le_div_of_nonneg_right (by exact_mod_cast nonzero_fiber_card_le_nine scalar)
    (by norm_num [Scalar.modulus])

/-- Each history is fixed before the fresh answer is sampled. Its chosen
target may depend arbitrarily on all prior answers. The explicit uniform
fresh-answer model is conditionalHitFraction; interpreting a real oracle by
this model is an independent ideal-hash/game contract. -/
structure Attempt (History : Type) [Fintype History] where
  historyWeight : History → ℚ
  nonnegative : ∀ history, 0 ≤ historyWeight history
  total : ∑ history, historyWeight history = 1
  target : History → Nat

def attemptHit {History : Type} [Fintype History] (attempt : Attempt History) : ℚ :=
  ∑ history, attempt.historyWeight history * conditionalHitFraction (attempt.target history)

private theorem sum_mono {I : Type} [DecidableEq I] (items : Finset I) (left right : I → ℚ)
    (each : ∀ item ∈ items, left item ≤ right item) :
    (∑ item ∈ items, left item) ≤ ∑ item ∈ items, right item := by
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item rest absent ih =>
      rw [Finset.sum_insert absent,Finset.sum_insert absent]
      exact add_le_add (each item (Finset.mem_insert_self _ _))
        (ih (by intro previous present; exact each previous (Finset.mem_insert_of_mem present)))

private theorem sum_times {I : Type} [DecidableEq I] (items : Finset I) (term : I → ℚ) (coefficient : ℚ) :
    (∑ item ∈ items, term item * coefficient) = (∑ item ∈ items, term item) * coefficient := by
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item rest absent ih => simp only [Finset.sum_insert absent,ih,add_mul]

theorem adaptive_attempt_bound {History : Type} [Fintype History] (attempt : Attempt History) :
    attemptHit attempt ≤ bound := by
  classical
  calc
    attemptHit attempt ≤ ∑ history, attempt.historyWeight history * bound := by
      exact sum_mono _ _ _ (fun history _ =>
        mul_le_mul_of_nonneg_left (conditional_hit_bound (attempt.target history)) (attempt.nonnegative history))
    _ = bound := by rw [sum_times,attempt.total,one_mul]

/-- Finite probability space. Weights need not be uniform or independent.
Only the per-query distribution bridge below introduces the ideal fresh-query
model. This definition supplies the union bound instead of assuming it. -/
structure FiniteExperiment (Sample : Type) [Fintype Sample] where
  weight : Sample → ℚ
  nonnegative : ∀ sample, 0 ≤ weight sample
  total : ∑ sample, weight sample = 1

def eventProbability {Sample : Type} [Fintype Sample] (experiment : FiniteExperiment Sample)
    (event : Sample → Bool) : ℚ :=
  ∑ sample, if event sample then experiment.weight sample else 0

def anyHit {Sample : Type} (queries : List (Sample → Bool)) : Sample → Bool :=
  fun sample => queries.any (fun event => event sample)

theorem event_union_bound {Sample : Type} [Fintype Sample]
    (experiment : FiniteExperiment Sample) (left right : Sample → Bool) :
    eventProbability experiment (fun sample => left sample || right sample) ≤
      eventProbability experiment left + eventProbability experiment right := by
  classical
  rw [eventProbability,eventProbability,eventProbability,← Finset.sum_add_distrib]
  apply sum_mono
  intro sample _
  have nonnegative := experiment.nonnegative sample
  cases left sample <;> cases right sample <;> simp_all

theorem finite_query_union_bound {Sample : Type} [Fintype Sample]
    (experiment : FiniteExperiment Sample) (queries : List (Sample → Bool)) :
    eventProbability experiment (anyHit queries) ≤
      (queries.map (eventProbability experiment)).sum := by
  induction queries with
  | nil => simp [eventProbability,anyHit]
  | cons event tail ih =>
      have union := event_union_bound experiment event (anyHit tail)
      change eventProbability experiment (fun sample => event sample || anyHit tail sample) ≤
        eventProbability experiment event + (tail.map (eventProbability experiment)).sum
      exact union.trans (add_le_add le_rfl ih)

private theorem sum_event_bounds {Sample : Type} [Fintype Sample]
    (experiment : FiniteExperiment Sample) (queries : List (Sample → Bool))
    (each : ∀ event ∈ queries, eventProbability experiment event ≤ bound) :
    (queries.map (eventProbability experiment)).sum ≤ (queries.length : ℚ) * bound := by
  induction queries with
  | nil => simp
  | cons event tail ih =>
      have head := each event (List.mem_cons_self)
      have rest := ih (by intro event member; exact each event (List.mem_cons_of_mem _ member))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      calc
        _ ≤ bound + (tail.length : ℚ) * bound := add_le_add head rest
        _ = _ := by ring

/-- This theorem counts actual Boolean events on a finite experiment. The
distribution premise identifies each fresh-query event with its pre-answer
history experiment; it must be established by the explicit ideal-hash game.
Repeated queries, domain/key encoding, subgroup/extraction prerequisites and
the reduction from a Transfer ownership failure to these events remain separate
obligations. No universal hash injectivity or concrete-Poseidon RO conclusion
is assumed or proved here. -/
theorem fresh_query_bound {Sample History : Type} [Fintype Sample] [Fintype History]
    (experiment : FiniteExperiment Sample) (queries : List (Sample → Bool))
    (attempts : (Sample → Bool) → Attempt History)
    (freshDistribution : ∀ event ∈ queries,
      eventProbability experiment event = attemptHit (attempts event)) :
    eventProbability experiment (anyHit queries) ≤ (queries.length : ℚ) * bound := by
  have each : ∀ event ∈ queries, eventProbability experiment event ≤ bound := by
    intro event member
    rw [freshDistribution event member]
    exact adaptive_attempt_bound (attempts event)
  exact (finite_query_union_bound experiment queries).trans (sum_event_bounds experiment queries each)

set_option pp.all true in
#check @nonzero_fiber_card_le_nine
#print axioms nonzero_fiber_card_le_nine
set_option pp.all true in
#check @conditional_hit_bound
#print axioms conditional_hit_bound
set_option pp.all true in
#check @adaptive_attempt_bound
#print axioms adaptive_attempt_bound
set_option pp.all true in
#check @event_union_bound
#print axioms event_union_bound
set_option pp.all true in
#check @finite_query_union_bound
#print axioms finite_query_union_bound
set_option pp.all true in
#check @fresh_query_bound
#print axioms fresh_query_bound

end ShielddSecurity.TransferReducedKeyQueries
