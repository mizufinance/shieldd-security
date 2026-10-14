import ShielddSecurity.SharedWordWitness221
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TierFlagLayout620
def columns : List Nat := List.range' 7597 11
def flags : List Nat := [7597,7599,7601,7603,7605,7606]
def plain : List Nat := [7598,7600,7602,7604,7607]
def outside (column : Nat) : Bool := plain.all (fun target => decide (column≠target))
theorem bounds (column : Nat) (member : column∈columns) : 7597≤column ∧ column<7608 := by
  obtain ⟨offset,before,equal⟩ := List.mem_range'.mp member
  simp only [Nat.one_mul] at equal
  omega
theorem plain_columns (column : Nat) (member : column∈plain) : column∈columns := by
  have checked : plain.all (fun col => decide (col∈columns))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
end ShielddSecurity.TierFlagLayout620
set_option pp.all true in
#check @ShielddSecurity.TierFlagLayout620.bounds
#print axioms ShielddSecurity.TierFlagLayout620.bounds
set_option pp.all true in
#check @ShielddSecurity.TierFlagLayout620.plain_columns
#print axioms ShielddSecurity.TierFlagLayout620.plain_columns
