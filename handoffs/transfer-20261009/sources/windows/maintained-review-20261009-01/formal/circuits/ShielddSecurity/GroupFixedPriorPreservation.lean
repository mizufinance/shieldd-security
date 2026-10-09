import ShielddSecurity.GroupFixedCircuitBounds

set_option maxHeartbeats 200000

namespace ShielddSecurity.GroupFixedPriorPreservation

open GroupFixedCircuitCompletion

variable {F : Type} [Field F]

/-- Advance the two allocation cursors without walking the prior relation. -/
theorem rows_covered_mono (highStart copy : Nat)
    (before after : GroupFixedCircuitBounds.Frame) (prior : List Row)
    (growth : before.low ≤ after.low ∧ before.high ≤ after.high)
    (covered : GroupFixedCircuitBounds.RowsCovered highStart copy before prior) :
    GroupFixedCircuitBounds.RowsCovered highStart copy after prior := by
  intro row member term present
  rcases covered row member term present with low | high | copied
  · exact Or.inl (Nat.lt_of_lt_of_le low growth.1)
  · exact Or.inr (Or.inl ⟨high.1, Nat.lt_of_lt_of_le high.2 growth.2⟩)
  · exact Or.inr (Or.inr copied)

/-- Freshness transports the values read by every preceding physical row.
No legality, endpoint meaning, or truth of newly emitted rows is assumed. -/
theorem run_agrees_prior (rho : Nat → F) (programs : List Program)
    (prior : List Row) (fresh : Fresh prior programs) :
    ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b,
      run rho programs term.1 = rho term.1 := by
  induction programs generalizing rho prior with
  | nil => intro row member term present; rfl
  | cons program tail ih =>
      intro row member term present
      have remaining := ih (program.build rho) (prior ++ program.rows) fresh.2
        row (List.mem_append_left program.rows member) term present
      exact remaining.trans (GroupCircuitOrder.run_outside rho program.stages term.1
        (fresh.1 row member term present))

/-- Preserve an independently constructed preceding relation through a loop.
The concrete caller must prove freshness from its actual row/write supports. -/
theorem run_preserves_prior (rho : Nat → F) (programs : List Program)
    (prior : List Row) (fresh : Fresh prior programs) (initial : Satisfies rho prior) :
    Satisfies (run rho programs) prior := by
  intro row member
  have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (run rho programs) terms = eval rho terms := by
    apply eval_agrees
    intro term present
    exact run_agrees_prior rho programs prior fresh row member term (inside term present)
  change Square (eval (run rho programs) row.a) (eval (run rho programs) row.b)
  rw [agrees row.a (by intro term present; exact List.mem_append_left row.b present),
    agrees row.b (by intro term present; exact List.mem_append_right row.a present)]
  exact initial row member

set_option pp.all true in
#check @rows_covered_mono
#print axioms rows_covered_mono
set_option pp.all true in
#check @run_agrees_prior
#print axioms run_agrees_prior
set_option pp.all true in
#check @run_preserves_prior
#print axioms run_preserves_prior

end ShielddSecurity.GroupFixedPriorPreservation
