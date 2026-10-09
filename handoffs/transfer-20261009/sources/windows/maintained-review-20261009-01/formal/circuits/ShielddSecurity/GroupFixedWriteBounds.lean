import ShielddSecurity.GroupFixedCircuitBounds

set_option maxHeartbeats 150000

namespace ShielddSecurity.GroupFixedWriteBounds

open GroupFixedCircuitBounds

theorem covers_mono (origin copy : Nat) (before after : Frame)
    (growth : before.low ≤ after.low ∧ before.high ≤ after.high)
    (column : Nat) (covered : covers origin copy before column) :
    covers origin copy after column := by
  rcases covered with low | high | copied
  · exact Or.inl (Nat.lt_of_lt_of_le low growth.1)
  · exact Or.inr (Or.inl ⟨high.1, Nat.lt_of_lt_of_le high.2 growth.2⟩)
  · exact Or.inr (Or.inr copied)

/-- A symbolic recurrence transports an earlier column through every local
allocation certificate, without expanding the concrete window list. -/
theorem certified_writes_outside (origin copy : Nat) (before : Frame)
    (segments : List (GroupFixedCircuitCompletion.Program × Frame))
    (certified : Certified origin copy before segments)
    (column : Nat) (covered : covers origin copy before column) :
    column ∉ segments.flatMap (fun segment =>
      segment.1.stages.flatMap GroupCircuitCompletion.Step.writes) := by
  induction segments generalizing before with
  | nil => simp only [List.flatMap_nil, List.not_mem_nil, not_false_eq_true]
  | cons segment tail ih =>
      rcases segment with ⟨program, after⟩
      rcases certified with ⟨growth, localRows, outside, remaining⟩
      intro written
      rcases List.mem_append.mp written with current | later
      · obtain ⟨stage, present, owned⟩ := List.mem_flatMap.mp current
        exact outside stage present column owned covered
      · exact ih after remaining (covers_mono origin copy before after growth column covered) later

set_option pp.all true in
#check @covers_mono
#print axioms covers_mono
set_option pp.all true in
#check @certified_writes_outside
#print axioms certified_writes_outside

end ShielddSecurity.GroupFixedWriteBounds
