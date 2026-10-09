import ShielddSecurity.TransferReducedKeyQueries

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferReducedKeyFreshOracle

open scoped BigOperators
open TransferReducedKeyCounting TransferReducedKeyQueries

local instance : IsOrderedAddMonoid ℚ where
  add_le_add_left := fun _ _ inequality _ => Rat.add_le_add_right.2 inequality

local instance : IsStrictOrderedRing ℚ := .of_mul_pos fun _ _ positiveLeft positiveRight ↦
  (Rat.mul_nonneg positiveLeft.le positiveRight.le).lt_of_ne'
    (mul_ne_zero positiveLeft.ne' positiveRight.ne')

def answerFraction (predicate : NonzeroOutput → Bool) : ℚ :=
  (Fintype.card {answer : NonzeroOutput // predicate answer = true} : ℚ) /
    (Fintype.card NonzeroOutput : ℚ)

private def hitEquiv (scalar : Nat) :
    {answer : NonzeroOutput // decide (answer.val.val % Scalar.order = scalar) = true} ≃
      NonzeroFiber scalar where
  toFun answer := ⟨answer.val,of_decide_eq_true answer.property⟩
  invFun answer := ⟨answer.val,by simpa only [decide_eq_true_eq] using answer.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem hit_answer_fraction (scalar : Nat) :
    answerFraction (fun answer => decide (answer.val.val % Scalar.order = scalar)) =
      conditionalHitFraction scalar := by
  unfold answerFraction conditionalHitFraction
  rw [Fintype.card_congr (hitEquiv scalar)]

/-- An explicit ideal fresh-answer contract, quantified over EVERY predicate
of pre-answer history and canonical nonzero field answer. It specifies the
joint history/answer distribution independently of collisions or security
events. A concrete oracle interpretation must establish this universal law;
the record cannot be instantiated merely from a selected event's desired
probability or from reduced-key fiber counting. -/
structure FreshQuery {Sample History : Type} [Fintype Sample] [Fintype History]
    (experiment : FiniteExperiment Sample) where
  attempt : Attempt History
  history : Sample → History
  answer : Sample → NonzeroOutput
  uniformLaw : ∀ predicate : History → NonzeroOutput → Bool,
    eventProbability experiment (fun sample => predicate (history sample) (answer sample)) =
      ∑ past, attempt.historyWeight past * answerFraction (predicate past)

variable {Sample History : Type} [Fintype Sample] [Fintype History]
  {experiment : FiniteExperiment Sample}

def hit (query : FreshQuery (History := History) experiment) : Sample → Bool :=
  fun sample => decide ((query.answer sample).val.val % Scalar.order =
    query.attempt.target (query.history sample))

theorem fresh_query_probability (query : FreshQuery (History := History) experiment) :
    eventProbability experiment (hit query) = attemptHit query.attempt := by
  have uniform := query.uniformLaw (fun past answer =>
    decide (answer.val.val % Scalar.order = query.attempt.target past))
  simpa only [hit,attemptHit,hit_answer_fraction] using uniform

theorem fresh_query_hit_bound (query : FreshQuery (History := History) experiment) :
    eventProbability experiment (hit query) ≤ bound :=
  (fresh_query_probability query).le.trans (adaptive_attempt_bound query.attempt)

/-- Fully adaptive targets are functions of the pre-answer history. Query
independence is unnecessary: each query's universal fresh conditional law
suffices. The application still owes freshness/repeated-query bookkeeping,
source domain/key encoding, subgroup and extraction prerequisites, and an
ownership-failure reduction. The concrete Poseidon function is not asserted
to satisfy the ideal fresh-answer record. -/
theorem fresh_queries_union_bound (queries : List (FreshQuery (History := History) experiment)) :
    eventProbability experiment (anyHit (queries.map hit)) ≤ (queries.length : ℚ) * bound := by
  have summed : ((queries.map hit).map (eventProbability experiment)).sum ≤
      (queries.length : ℚ) * bound := by
    induction queries with
    | nil => simp
    | cons query tail ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
        calc
          _ ≤ bound + (tail.length : ℚ) * bound := add_le_add (fresh_query_hit_bound query) ih
          _ = _ := by ring
  exact (finite_query_union_bound experiment (queries.map hit)).trans summed

set_option pp.all true in
#check @hit_answer_fraction
#print axioms hit_answer_fraction
set_option pp.all true in
#check @fresh_query_probability
#print axioms fresh_query_probability
set_option pp.all true in
#check @fresh_query_hit_bound
#print axioms fresh_query_hit_bound
set_option pp.all true in
#check @fresh_queries_union_bound
#print axioms fresh_queries_union_bound

end ShielddSecurity.TransferReducedKeyFreshOracle
