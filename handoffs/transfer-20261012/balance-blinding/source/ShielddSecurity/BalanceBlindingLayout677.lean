import ShielddSecurity.ComparisonBorrowFrame324
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingLayout677
def starts : List Nat := [22484]
def Inside (column : Nat) : Prop := ∃ start∈starts, start≤column ∧ column<start+252
def outside (column : Nat) : Bool := starts.all (fun start => decide (column<start ∨ start+252≤column))
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False := by
  obtain ⟨start,member,lower,upper⟩ := inside
  have separate := of_decide_eq_true (List.all_eq_true.mp checked start member)
  omega
theorem bounds (column : Nat) (inside : Inside column) : 22484≤column ∧ column<22736 := by
  obtain ⟨start,member,lower,upper⟩ := inside
  simp only [starts,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with rfl <;> omega
end ShielddSecurity.BalanceBlindingLayout677
set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingLayout677.starts
#print axioms ShielddSecurity.BalanceBlindingLayout677.starts
set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingLayout677.excluded
#print axioms ShielddSecurity.BalanceBlindingLayout677.excluded
set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingLayout677.bounds
#print axioms ShielddSecurity.BalanceBlindingLayout677.bounds
