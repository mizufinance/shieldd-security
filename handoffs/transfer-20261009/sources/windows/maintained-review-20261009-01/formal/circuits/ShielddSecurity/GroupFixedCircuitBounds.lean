import ShielddSecurity.GroupFixedCircuitCompletion

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupFixedCircuitBounds

open GroupFixedCircuitCompletion

structure Frame where
  low : Nat
  high : Nat

/-- Actual witness and compiler-product allocations advance separately. The
constant-copy column remains protected even though it is above both cursors. -/
def covers (highStart copy : Nat) (frame : Frame) (column : Nat) : Prop :=
  column < frame.low ∨ (highStart ≤ column ∧ column < frame.high) ∨ column = copy

instance (highStart copy : Nat) (frame : Frame) (column : Nat) :
    Decidable (covers highStart copy frame column) :=
  inferInstanceAs (Decidable
    (column < frame.low ∨ (highStart ≤ column ∧ column < frame.high) ∨ column = copy))

def RowsCovered (highStart copy : Nat) (frame : Frame) (rows : List Row) : Prop :=
  ∀ row ∈ rows, ∀ term ∈ row.a ++ row.b, covers highStart copy frame term.1

def WritesOutside (highStart copy : Nat) (frame : Frame) (program : Program) : Prop :=
  ∀ stage ∈ program.stages, ∀ column ∈ stage.writes,
    ¬ covers highStart copy frame column

/-- Only a single bounded window is checked. Earlier rows are transported by
the monotone support lemma below, rather than checked again at each window. -/
def checkLocal (highStart copy : Nat) (before after : Frame) (program : Program) : Bool :=
  decide (before.low ≤ after.low ∧ before.high ≤ after.high) &&
    program.rows.all (fun row => (row.a ++ row.b).all
      (fun term => decide (covers highStart copy after term.1))) &&
    program.stages.all (fun stage => stage.writes.all
      (fun column => decide (¬ covers highStart copy before column)))

theorem checked_local (highStart copy : Nat) (before after : Frame) (program : Program)
    (checked : checkLocal highStart copy before after program = true) :
    (before.low ≤ after.low ∧ before.high ≤ after.high) ∧
      RowsCovered highStart copy after program.rows ∧
      WritesOutside highStart copy before program := by
  simp only [checkLocal, Bool.and_eq_true, decide_eq_true_eq] at checked
  refine ⟨checked.1.1, ?_, ?_⟩
  · intro row member term present
    exact of_decide_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp checked.1.2 row member) term present)
  · intro stage member column written
    exact of_decide_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp checked.2 stage member) column written)

def Certified (highStart copy : Nat) (before : Frame) : List (Program × Frame) → Prop
  | [] => True
  | (program, after) :: tail =>
      (before.low ≤ after.low ∧ before.high ≤ after.high) ∧
        RowsCovered highStart copy after program.rows ∧
        WritesOutside highStart copy before program ∧ Certified highStart copy after tail

private theorem covers_mono (highStart copy : Nat) (before after : Frame)
    (growth : before.low ≤ after.low ∧ before.high ≤ after.high) (column : Nat)
    (covered : covers highStart copy before column) : covers highStart copy after column := by
  rcases covered with low | high | copied
  · exact Or.inl (Nat.lt_of_lt_of_le low growth.1)
  · exact Or.inr (Or.inl ⟨high.1, Nat.lt_of_lt_of_le high.2 growth.2⟩)
  · exact Or.inr (Or.inr copied)

/-- Exact freshness of all preceding original rows follows by list induction
from local write/support checks. No row satisfaction or desired output is a
premise; the actual loop still supplies all local constructor proofs. -/
theorem bounded_fresh (highStart copy : Nat) (before : Frame) (prior : List Row)
    (segments : List (Program × Frame))
    (initial : RowsCovered highStart copy before prior)
    (certificate : Certified highStart copy before segments) :
    Fresh prior (segments.map Prod.fst) := by
  induction segments generalizing before prior with
  | nil => trivial
  | cons segment tail ih =>
      rcases segment with ⟨program, after⟩
      rcases certificate with ⟨growth, localRows, outside, remaining⟩
      refine ⟨?_, ih after (prior ++ program.rows) ?_ remaining⟩
      · intro row member term present stage stageMember written
        exact outside stage stageMember term.1 written (initial row member term present)
      · intro row member term present
        rcases List.mem_append.mp member with previous | current
        · exact covers_mono highStart copy before after growth term.1
            (initial row previous term present)
        · exact localRows row current term present

set_option pp.all true in
#check @checked_local
#print axioms checked_local
set_option pp.all true in
#check @bounded_fresh
#print axioms bounded_fresh

end ShielddSecurity.GroupFixedCircuitBounds
