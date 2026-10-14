import ShielddSecurity.FixedFamilyLayout545
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublishedInverseLayout589
def starts : List Nat := [5435,6839,9056,10588,12116,14134,15396,16658]
def pointStart (family : Fin 8) : Nat := starts[family.val]!
def Inside (column : Nat) : Prop := ∃ start∈starts, start≤column ∧ column<start+1
def outside (column : Nat) : Bool := starts.all (fun start => decide (column<start ∨ start+1≤column))
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False := by
  obtain ⟨start,member,lower,upper⟩ := inside
  have separate := of_decide_eq_true (List.all_eq_true.mp checked start member)
  omega
theorem bounds (column : Nat) (inside : Inside column) : 5435≤column ∧ column<16659 := by
  obtain ⟨start,member,lower,upper⟩ := inside
  simp only [starts,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
end ShielddSecurity.PublishedInverseLayout589
set_option pp.all true in
#check @ShielddSecurity.PublishedInverseLayout589.starts
#print axioms ShielddSecurity.PublishedInverseLayout589.starts
set_option pp.all true in
#check @ShielddSecurity.PublishedInverseLayout589.excluded
#print axioms ShielddSecurity.PublishedInverseLayout589.excluded
set_option pp.all true in
#check @ShielddSecurity.PublishedInverseLayout589.bounds
#print axioms ShielddSecurity.PublishedInverseLayout589.bounds
