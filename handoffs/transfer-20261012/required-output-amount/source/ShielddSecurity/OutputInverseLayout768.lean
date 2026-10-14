import ShielddSecurity.ComparisonBorrowFrame324
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OutputInverseLayout768
-- The required output amount inverse witness is outside all Boolean and word windows.
def values : List Nat := [4919]
def Inside (column : Nat) : Prop := column∈values
def outside (column : Nat) : Bool := decide (column∉values)
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False :=
  (of_decide_eq_true checked) inside
theorem bounds (column : Nat) (inside : Inside column) : 4919≤column ∧ column<4920 := by
  have checked : values.all (fun n => decide (4919≤n ∧ n<4920))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked column inside)
end ShielddSecurity.OutputInverseLayout768

set_option pp.all true in
#check @ShielddSecurity.OutputInverseLayout768.values
#print axioms ShielddSecurity.OutputInverseLayout768.values

set_option pp.all true in
#check @ShielddSecurity.OutputInverseLayout768.excluded
#print axioms ShielddSecurity.OutputInverseLayout768.excluded

set_option pp.all true in
#check @ShielddSecurity.OutputInverseLayout768.bounds
#print axioms ShielddSecurity.OutputInverseLayout768.bounds
