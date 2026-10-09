import ShielddSecurity.GroupFixedCircuitBounds

set_option maxHeartbeats 200000

namespace ShielddSecurity.GroupCircuitFrameTrace

open GroupFixedCircuitCompletion GroupFixedCircuitBounds

def lastFrame (before : Frame) : List (Program × Frame) → Frame
  | [] => before
  | segment :: tail => lastFrame segment.2 tail

/-- Eight bounded frame certificates compose without expanding their rows or
repeating any scalar-loop proof. This rule speaks only about actual support and
write fences, independently of physical compiler allocation interpretation. -/
theorem certified_append (highStart copy : Nat) (before : Frame)
    (left right : List (Program × Frame)) :
    Certified highStart copy before (left ++ right) ↔
      Certified highStart copy before left ∧
        Certified highStart copy (lastFrame before left) right := by
  induction left generalizing before with
  | nil => simp only [List.nil_append, Certified, lastFrame, true_and]
  | cons segment tail ih =>
    rcases segment with ⟨program, after⟩
    change ((before.low ≤ after.low ∧ before.high ≤ after.high) ∧
      RowsCovered highStart copy after program.rows ∧
      WritesOutside highStart copy before program ∧
      Certified highStart copy after (tail ++ right)) ↔
      ((before.low ≤ after.low ∧ before.high ≤ after.high) ∧
        RowsCovered highStart copy after program.rows ∧
        WritesOutside highStart copy before program ∧
        Certified highStart copy after tail) ∧
        Certified highStart copy (lastFrame after tail) right
    constructor
    · rintro ⟨growth, localRows, outside, rest⟩
      have split := (ih after).mp rest
      exact ⟨⟨growth, localRows, outside, split.1⟩,split.2⟩
    · rintro ⟨⟨growth, localRows, outside, pastFrame⟩, suffix⟩
      exact ⟨growth, localRows, outside, (ih after).mpr ⟨pastFrame,suffix⟩⟩

private theorem covered_mono (highStart copy : Nat) (before after : Frame)
    (growth : before.low ≤ after.low ∧ before.high ≤ after.high) (column : Nat)
    (inside : covers highStart copy before column) :
    covers highStart copy after column := by
  rcases inside with low | high | copied
  · exact Or.inl (Nat.lt_of_lt_of_le low growth.1)
  · exact Or.inr (Or.inl ⟨high.1,Nat.lt_of_lt_of_le high.2 growth.2⟩)
  · exact Or.inr (Or.inr copied)

theorem rows_covered_final (highStart copy : Nat) (before : Frame) (prior : List Row)
    (segments : List (Program × Frame))
    (initial : RowsCovered highStart copy before prior)
    (certificate : Certified highStart copy before segments) :
    RowsCovered highStart copy (lastFrame before segments)
      (prior ++ rows (segments.map Prod.fst)) := by
  induction segments generalizing before prior with
  | nil => simpa only [List.map_nil, rows, List.append_nil, lastFrame] using initial
  | cons segment tail ih =>
    rcases segment with ⟨program,after⟩
    rcases certificate with ⟨growth,localRows,outside,remaining⟩
    have combined : RowsCovered highStart copy after (prior ++ program.rows) := by
      intro row member term present
      rcases List.mem_append.mp member with previous | current
      · exact covered_mono highStart copy before after growth term.1
          (initial row previous term present)
      · exact localRows row current term present
    have result := ih after (prior ++ program.rows) combined remaining
    simpa only [lastFrame,List.map_cons,rows,List.append_assoc] using result

set_option pp.all true in
#check @certified_append
#print axioms certified_append
set_option pp.all true in
#check @rows_covered_final
#print axioms rows_covered_final

end ShielddSecurity.GroupCircuitFrameTrace
