import ShielddSecurity.TierGroupDomain612
import ShielddSecurity.SharedScalarCanonical396
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierLayout613
def starts : List Nat := [12117,12873,14135,15397,16659]
def pointStart (family : Fin 5) : Nat := starts[family.val]!
def scalarFamily (family : Fin 5) : Fin 9 := ⟨if family.val<2 then 5 else family.val+4,by split <;> omega⟩
def scalar (w : TransferSem.Witness) (family : Fin 5) : Nat :=
  SharedScalarCanonical396.numbers w (scalarFamily family)
def Inside (column : Nat) : Prop := ∃ start∈starts, start≤column ∧ column<start+756
def outside (column : Nat) : Bool := starts.all (fun start => decide (column<start ∨ start+756≤column))
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False := by
  obtain ⟨start,member,lower,upper⟩ := inside
  have separate := of_decide_eq_true (List.all_eq_true.mp checked start member)
  omega
theorem bounds (column : Nat) (inside : Inside column) : 12117≤column ∧ column<17415 := by
  obtain ⟨start,member,lower,upper⟩ := inside
  simp only [starts,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl <;> omega
end ShielddSecurity.TierLayout613
set_option pp.all true in
#check @ShielddSecurity.TierLayout613.starts
#print axioms ShielddSecurity.TierLayout613.starts
set_option pp.all true in
#check @ShielddSecurity.TierLayout613.scalar
#print axioms ShielddSecurity.TierLayout613.scalar
set_option pp.all true in
#check @ShielddSecurity.TierLayout613.excluded
#print axioms ShielddSecurity.TierLayout613.excluded
set_option pp.all true in
#check @ShielddSecurity.TierLayout613.bounds
#print axioms ShielddSecurity.TierLayout613.bounds
