import ShielddSecurity.Rows

set_option maxHeartbeats 100000

namespace ShielddSecurity.ColumnFence

/-- Actual column bounds, not an assumption about compiler allocation order.
The outlined constant copy may be larger than fresh columns but is kept. -/
def checkWrites (copy floor : Nat) (writes : List Nat) : Bool :=
  writes.all (fun column => decide (floor ≤ column ∧ column ≠ copy))

def checkRows (copy floor : Nat) (rows : List Row) : Bool :=
  rows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 = copy ∨ term.1 < floor)))

theorem checked_column (copy floor : Nat) (writes : List Nat) (column : Nat)
    (checked : checkWrites copy floor writes = true)
    (below : column = copy ∨ column < floor) : column ∉ writes := by
  intro member
  have lower := of_decide_eq_true (List.all_eq_true.mp checked column member)
  rcases below with fixed | small
  · exact lower.2 fixed
  · exact (Nat.not_lt_of_ge lower.1) small

/-- A linear scan of captured supports avoids a product of previous-row terms
and current writes when sequencing many native hash/tree calls. -/
theorem checked_rows (copy floor : Nat) (writes : List Nat) (rows : List Row)
    (lower : checkWrites copy floor writes = true) (upper : checkRows copy floor rows = true) :
    ∀ row ∈ rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ writes := by
  intro row member term present
  exact checked_column copy floor writes term.1 lower
    (of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp upper) row member)) term present))

set_option pp.all true in
#check @checked_column
#print axioms checked_column
set_option pp.all true in
#check @checked_rows
#print axioms checked_rows

end ShielddSecurity.ColumnFence
