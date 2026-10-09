import ShielddSecurity.GroupFixedCircuitBounds

set_option maxHeartbeats 100000
set_option maxRecDepth 2048

namespace ShielddSecurity.GroupFrameExceptions

open GroupFixedCircuitBounds

/-- Native publication/inverse witnesses may be allocated before the next
bit/ compiler cursors. Those few actual writes are excluded from earlier row
supports independently; no row satisfaction or point equation is checked. -/
def checkWrites (origin copy : Nat) (frame : Frame) (exceptions writes : List Nat) : Bool :=
  writes.all (fun column => decide (¬ covers origin copy frame column ∨ column ∈ exceptions))

def checkRows (origin copy : Nat) (frame : Frame) (exceptions : List Nat) (rows : List Row) : Bool :=
  rows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (covers origin copy frame term.1 ∧ term.1 ∉ exceptions)))

theorem checked_column (origin copy : Nat) (frame : Frame) (exceptions writes : List Nat)
    (column : Nat) (checked : checkWrites origin copy frame exceptions writes = true)
    (preserved : covers origin copy frame column ∧ column ∉ exceptions) : column ∉ writes := by
  intro member
  have alternative := of_decide_eq_true (List.all_eq_true.mp checked column member)
  rcases alternative with outside | exceptional
  · exact outside preserved.1
  · exact preserved.2 exceptional

theorem checked_rows (origin copy : Nat) (frame : Frame) (exceptions writes : List Nat) (rows : List Row)
    (lower : checkWrites origin copy frame exceptions writes = true)
    (upper : checkRows origin copy frame exceptions rows = true) :
    ∀ row ∈ rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ writes := by
  intro row member term present
  exact checked_column origin copy frame exceptions writes term.1 lower
    (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp upper row member) term present))

set_option pp.all true in
#check @checked_column
#print axioms checked_column
set_option pp.all true in
#check @checked_rows
#print axioms checked_rows

end ShielddSecurity.GroupFrameExceptions
