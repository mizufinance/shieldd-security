import ShielddSecurity.FixedFamilyLayout545
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublishedPointLayout581
def starts : List Nat := [4922,6326,8547,10079,8515,8520,8526,8531]
def pointStart (family : Fin 8) : Nat := starts[family.val]!
def Inside (column : Nat) : Prop := ∃ start∈starts, start≤column ∧ column<start+2
def outside (column : Nat) : Bool := starts.all (fun start => decide (column<start ∨ start+2≤column))
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False := by
  obtain ⟨start,member,lower,upper⟩ := inside
  have separate := of_decide_eq_true (List.all_eq_true.mp checked start member)
  omega
theorem bounds (column : Nat) (inside : Inside column) : 4922≤column ∧ column<10081 := by
  obtain ⟨start,member,lower,upper⟩ := inside
  simp only [starts,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
end ShielddSecurity.PublishedPointLayout581
set_option pp.all true in
#check @ShielddSecurity.PublishedPointLayout581.starts
#print axioms ShielddSecurity.PublishedPointLayout581.starts
set_option pp.all true in
#check @ShielddSecurity.PublishedPointLayout581.excluded
#print axioms ShielddSecurity.PublishedPointLayout581.excluded
set_option pp.all true in
#check @ShielddSecurity.PublishedPointLayout581.bounds
#print axioms ShielddSecurity.PublishedPointLayout581.bounds
