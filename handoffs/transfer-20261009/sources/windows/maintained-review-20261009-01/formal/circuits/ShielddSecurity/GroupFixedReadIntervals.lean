import ShielddSecurity.GroupFixedCircuitCompletion

set_option maxHeartbeats 100000

namespace ShielddSecurity.GroupFixedReadIntervals

/-- Two finite regions cover the actual low and high allocation writes. -/
structure Regions where
  lowFirst : Nat
  lowLast : Nat
  highFirst : Nat
  highLast : Nat

def Outside (regions : Regions) (column : Nat) : Prop :=
  (column < regions.lowFirst ∨ regions.lowLast < column) ∧
  (column < regions.highFirst ∨ regions.highLast < column)

def Inside (regions : Regions) (column : Nat) : Prop :=
  (regions.lowFirst ≤ column ∧ column ≤ regions.lowLast) ∨
  (regions.highFirst ≤ column ∧ column ≤ regions.highLast)

instance (regions : Regions) (column : Nat) : Decidable (Outside regions column) :=
  inferInstanceAs (Decidable ((column < regions.lowFirst ∨ regions.lowLast < column) ∧
    (column < regions.highFirst ∨ regions.highLast < column)))

instance (regions : Regions) (column : Nat) : Decidable (Inside regions column) :=
  inferInstanceAs (Decidable ((regions.lowFirst ≤ column ∧ column ≤ regions.lowLast) ∨
    (regions.highFirst ≤ column ∧ column ≤ regions.highLast)))

theorem outside_disjoint (regions : Regions) (column : Nat)
    (outside : Outside regions column) (inside : Inside regions column) : False := by
  unfold Outside at outside
  unfold Inside at inside
  rcases inside with low | high
  · rcases outside.1 with before | after
    · exact (Nat.not_lt_of_ge low.1) before
    · exact (Nat.not_lt_of_ge low.2) after
  · rcases outside.2 with before | after
    · exact (Nat.not_lt_of_ge high.1) before
    · exact (Nat.not_lt_of_ge high.2) after

theorem protected_reads (regions : Regions) (kept : List Nat)
    (program : GroupFixedCircuitCompletion.Program)
    (reads : ∀ column ∈ kept, Outside regions column)
    (writes : ∀ stage ∈ program.stages, ∀ column ∈ stage.writes, Inside regions column) :
    GroupFixedCircuitCompletion.Protected kept program := by
  intro stage present column member written
  exact outside_disjoint regions column (reads column member) (writes stage present column written)

set_option pp.all true in
#check @outside_disjoint
#print axioms outside_disjoint
set_option pp.all true in
#check @protected_reads
#print axioms protected_reads

end ShielddSecurity.GroupFixedReadIntervals
