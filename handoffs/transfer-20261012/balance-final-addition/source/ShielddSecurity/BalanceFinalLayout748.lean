import ShielddSecurity.ComparisonBorrowFrame324
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceFinalLayout748
-- The final balance inverse witness is outside all Boolean and word windows.
def values : List Nat := [22736]
def Inside (column : Nat) : Prop := column∈values
def outside (column : Nat) : Bool := decide (column∉values)
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False :=
  (of_decide_eq_true checked) inside
theorem bounds (column : Nat) (inside : Inside column) : 22736≤column ∧ column<22737 := by
  have checked : values.all (fun n => decide (22736≤n ∧ n<22737))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked column inside)
end ShielddSecurity.BalanceFinalLayout748

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalLayout748.values
#print axioms ShielddSecurity.BalanceFinalLayout748.values

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalLayout748.excluded
#print axioms ShielddSecurity.BalanceFinalLayout748.excluded

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalLayout748.bounds
#print axioms ShielddSecurity.BalanceFinalLayout748.bounds
