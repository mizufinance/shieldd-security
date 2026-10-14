import ShielddSecurity.ComparisonBorrowFrame324
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.DetectionInverseLayout760
-- The selected detection inverse witness is outside all Boolean and word windows.
def values : List Nat := [1503]
def Inside (column : Nat) : Prop := column∈values
def outside (column : Nat) : Bool := decide (column∉values)
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False :=
  (of_decide_eq_true checked) inside
theorem bounds (column : Nat) (inside : Inside column) : 1503≤column ∧ column<1504 := by
  have checked : values.all (fun n => decide (1503≤n ∧ n<1504))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked column inside)
end ShielddSecurity.DetectionInverseLayout760

set_option pp.all true in
#check @ShielddSecurity.DetectionInverseLayout760.values
#print axioms ShielddSecurity.DetectionInverseLayout760.values

set_option pp.all true in
#check @ShielddSecurity.DetectionInverseLayout760.excluded
#print axioms ShielddSecurity.DetectionInverseLayout760.excluded

set_option pp.all true in
#check @ShielddSecurity.DetectionInverseLayout760.bounds
#print axioms ShielddSecurity.DetectionInverseLayout760.bounds
