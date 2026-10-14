import ShielddSecurity.SharedWordWitness221
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.BalanceSignLayout647
def columns : List Nat := List.range' 21711 1
def flags : List Nat := [21711]
def plain : List Nat := []
def outside (column : Nat) : Bool := plain.all (fun target => decide (column≠target))
theorem bounds (column : Nat) (member : column∈columns) : 21711≤column ∧ column<21712 := by
  obtain ⟨offset,before,equal⟩ := List.mem_range'.mp member
  simp only [Nat.one_mul] at equal
  omega
theorem plain_columns (column : Nat) (member : column∈plain) : column∈columns := by
  have checked : plain.all (fun col => decide (col∈columns))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
end ShielddSecurity.BalanceSignLayout647
set_option pp.all true in
#check @ShielddSecurity.BalanceSignLayout647.bounds
#print axioms ShielddSecurity.BalanceSignLayout647.bounds
set_option pp.all true in
#check @ShielddSecurity.BalanceSignLayout647.plain_columns
#print axioms ShielddSecurity.BalanceSignLayout647.plain_columns
