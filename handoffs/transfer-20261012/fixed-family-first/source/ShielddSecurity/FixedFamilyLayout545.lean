import ShielddSecurity.FixedFamilyJoin543
import ShielddSecurity.SharedScalarCanonical396
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamilyLayout545
def starts : List Nat := [5183,6587,8804,10336,11864,13882,15144,16406]
def pointStart (family : Fin 8) : Nat := starts[family.val]!
def scalarFamily (family : Fin 8) : Fin 9 := ⟨family.val+1,by omega⟩
def scalar (w : TransferSem.Witness) (family : Fin 8) : Nat :=
  SharedScalarCanonical396.numbers w (scalarFamily family)
def Inside (column : Nat) : Prop := ∃ start∈starts, start≤column ∧ column<start+252
def outside (column : Nat) : Bool := starts.all (fun start => decide (column<start ∨ start+252≤column))
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False := by
  obtain ⟨start,member,lower,upper⟩ := inside
  have separate := of_decide_eq_true (List.all_eq_true.mp checked start member)
  omega
theorem bounds (column : Nat) (inside : Inside column) : 5183≤column ∧ column<16658 := by
  obtain ⟨start,member,lower,upper⟩ := inside
  simp only [starts,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
end ShielddSecurity.FixedFamilyLayout545
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyLayout545.starts
#print axioms ShielddSecurity.FixedFamilyLayout545.starts
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyLayout545.scalar
#print axioms ShielddSecurity.FixedFamilyLayout545.scalar
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyLayout545.excluded
#print axioms ShielddSecurity.FixedFamilyLayout545.excluded
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyLayout545.bounds
#print axioms ShielddSecurity.FixedFamilyLayout545.bounds
