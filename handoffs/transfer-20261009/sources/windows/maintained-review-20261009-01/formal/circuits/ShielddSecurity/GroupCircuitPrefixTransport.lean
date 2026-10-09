import ShielddSecurity.GroupFrameTransport

set_option maxHeartbeats 150000

namespace ShielddSecurity.GroupCircuitPrefixTransport

open GroupFixedCircuitBounds GroupFixedCircuitCompletion

theorem rows_covered_mono (origin copy : Nat) (before after : Frame) (prior : List Row)
    (growth : before.low ≤ after.low ∧ before.high ≤ after.high)
    (covered : RowsCovered origin copy before prior) : RowsCovered origin copy after prior := by
  intro row member term present
  rcases covered row member term present with low | high | copied
  · exact Or.inl (Nat.lt_of_lt_of_le low growth.1)
  · exact Or.inr (Or.inl ⟨high.1,Nat.lt_of_lt_of_le high.2 growth.2⟩)
  · exact Or.inr (Or.inr copied)

/-- An independently constructed earlier prefix travels through any number of
bounded window programs. The certificate checks support/write exclusion; this
induction performs neither scalar unrolling nor a walk over earlier row bodies. -/
theorem certified_preserves {F : Type} [Field F] (origin copy : Nat) (before : Frame)
    (rho : Nat → F) (prior : List Row) (segments : List (Program × Frame))
    (covered : RowsCovered origin copy before prior)
    (certificate : Certified origin copy before segments) (constructed : Satisfies rho prior) :
    Satisfies (run rho (segments.map Prod.fst)) prior := by
  induction segments generalizing before rho with
  | nil => exact constructed
  | cons segment tail ih =>
    rcases segment with ⟨program,after⟩
    rcases certificate with ⟨growth,localRows,outside,remaining⟩
    have previous : Satisfies (program.build rho) prior :=
      GroupFrameTransport.run_preserves_rows rho program.stages origin copy before prior
        covered outside constructed
    change Satisfies (run (program.build rho) (tail.map Prod.fst)) prior
    exact ih after (program.build rho)
      (rows_covered_mono origin copy before after prior growth covered) remaining previous

set_option pp.all true in
#check @rows_covered_mono
#print axioms rows_covered_mono
set_option pp.all true in
#check @certified_preserves
#print axioms certified_preserves

end ShielddSecurity.GroupCircuitPrefixTransport
