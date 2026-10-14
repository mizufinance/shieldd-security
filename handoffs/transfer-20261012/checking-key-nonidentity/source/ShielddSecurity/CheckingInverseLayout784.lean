import ShielddSecurity.ComparisonBorrowFrame324
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CheckingInverseLayout784
-- The selected checking-key inverses witness is outside all Boolean and word windows.
def values : List Nat := [9057,10589]
def Inside (column : Nat) : Prop := column∈values
def outside (column : Nat) : Bool := decide (column∉values)
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False :=
  (of_decide_eq_true checked) inside
theorem bounds (column : Nat) (inside : Inside column) : 9057≤column ∧ column<10590 := by
  have checked : values.all (fun n => decide (9057≤n ∧ n<10590))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked column inside)
theorem alternatives (column : Nat) (inside : Inside column) : column=9057 ∨ column=10589 := by
  simpa only [Inside,values,List.mem_cons,List.not_mem_nil,or_false] using inside
end ShielddSecurity.CheckingInverseLayout784

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseLayout784.values
#print axioms ShielddSecurity.CheckingInverseLayout784.values

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseLayout784.excluded
#print axioms ShielddSecurity.CheckingInverseLayout784.excluded

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseLayout784.bounds
#print axioms ShielddSecurity.CheckingInverseLayout784.bounds

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseLayout784.alternatives
#print axioms ShielddSecurity.CheckingInverseLayout784.alternatives
