import ShielddSecurity.PayloadGroupDomain557
import ShielddSecurity.SharedScalarCanonical396
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadFamilyLayout559
def starts : List Nat := [5436,6840]
def pointStart (family : Fin 2) : Nat := starts[family.val]!
def scalarFamily (family : Fin 2) : Fin 9 := ⟨family.val+1,by omega⟩
def scalar (w : TransferSem.Witness) (family : Fin 2) : Nat :=
  SharedScalarCanonical396.numbers w (scalarFamily family)
def Inside (column : Nat) : Prop := ∃ start∈starts, start≤column ∧ column<start+756
def outside (column : Nat) : Bool := starts.all (fun start => decide (column<start ∨ start+756≤column))
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False := by
  obtain ⟨start,member,lower,upper⟩ := inside
  have separate := of_decide_eq_true (List.all_eq_true.mp checked start member)
  omega
theorem bounds (column : Nat) (inside : Inside column) : 5436≤column ∧ column<7596 := by
  obtain ⟨start,member,lower,upper⟩ := inside
  simp only [starts,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> omega
end ShielddSecurity.PayloadFamilyLayout559
set_option pp.all true in
#check @ShielddSecurity.PayloadFamilyLayout559.starts
#print axioms ShielddSecurity.PayloadFamilyLayout559.starts
set_option pp.all true in
#check @ShielddSecurity.PayloadFamilyLayout559.scalar
#print axioms ShielddSecurity.PayloadFamilyLayout559.scalar
set_option pp.all true in
#check @ShielddSecurity.PayloadFamilyLayout559.excluded
#print axioms ShielddSecurity.PayloadFamilyLayout559.excluded
set_option pp.all true in
#check @ShielddSecurity.PayloadFamilyLayout559.bounds
#print axioms ShielddSecurity.PayloadFamilyLayout559.bounds
