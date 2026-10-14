import ShielddSecurity.CheckingGroupDomain595
import ShielddSecurity.SharedScalarCanonical396
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipLayout600
def starts : List Nat := [9322,10854]
def pointStart (family : Fin 2) : Nat := starts[family.val]!
def scalarFamily (family : Fin 2) : Fin 9 := ⟨family.val+3,by omega⟩
def scalar (w : TransferSem.Witness) (family : Fin 2) : Nat :=
  SharedScalarCanonical396.numbers w (scalarFamily family)
def Inside (column : Nat) : Prop := ∃ start∈starts, start≤column ∧ column<start+756
def outside (column : Nat) : Bool := starts.all (fun start => decide (column<start ∨ start+756≤column))
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False := by
  obtain ⟨start,member,lower,upper⟩ := inside
  have separate := of_decide_eq_true (List.all_eq_true.mp checked start member)
  omega
theorem bounds (column : Nat) (inside : Inside column) : 9322≤column ∧ column<11610 := by
  obtain ⟨start,member,lower,upper⟩ := inside
  simp only [starts,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> omega
end ShielddSecurity.OwnershipLayout600
set_option pp.all true in
#check @ShielddSecurity.OwnershipLayout600.starts
#print axioms ShielddSecurity.OwnershipLayout600.starts
set_option pp.all true in
#check @ShielddSecurity.OwnershipLayout600.scalar
#print axioms ShielddSecurity.OwnershipLayout600.scalar
set_option pp.all true in
#check @ShielddSecurity.OwnershipLayout600.excluded
#print axioms ShielddSecurity.OwnershipLayout600.excluded
set_option pp.all true in
#check @ShielddSecurity.OwnershipLayout600.bounds
#print axioms ShielddSecurity.OwnershipLayout600.bounds
