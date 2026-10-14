import ShielddSecurity.SharedWordWitness221
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.RoutingPrecisionLayout808
def columns : List Nat := List.range' 19455 134
def flags : List Nat := List.range' 19457 66 2
def plain : List Nat := [19455,19456] ++ List.range' 19458 66 2
def outside (column : Nat) : Bool := plain.all (fun target => decide (column≠target))
theorem bounds (column : Nat) (member : column∈columns) : 19455≤column ∧ column<19589 := by
  obtain ⟨offset,before,equal⟩ := List.mem_range'.mp member
  simp only [Nat.one_mul] at equal
  omega
theorem plain_columns (column : Nat) (member : column∈plain) : column∈columns := by
  have checked : plain.all (fun col => decide (col∈columns))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
end ShielddSecurity.RoutingPrecisionLayout808
set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionLayout808.bounds
#print axioms ShielddSecurity.RoutingPrecisionLayout808.bounds
set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionLayout808.plain_columns
#print axioms ShielddSecurity.RoutingPrecisionLayout808.plain_columns
