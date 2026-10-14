import ShielddSecurity.ComparisonBorrowFrame324
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RecoveryInverseLayout775
-- The repeated recovery ephemeral-key inverses witness is outside all Boolean and word windows.
def values : List Nat := [6192,7596]
def Inside (column : Nat) : Prop := column∈values
def outside (column : Nat) : Bool := decide (column∉values)
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False :=
  (of_decide_eq_true checked) inside
theorem bounds (column : Nat) (inside : Inside column) : 6192≤column ∧ column<7597 := by
  have checked : values.all (fun n => decide (6192≤n ∧ n<7597))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked column inside)
theorem alternatives (column : Nat) (inside : Inside column) : column=6192 ∨ column=7596 := by
  simpa only [Inside,values,List.mem_cons,List.not_mem_nil,or_false] using inside
end ShielddSecurity.RecoveryInverseLayout775

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseLayout775.values
#print axioms ShielddSecurity.RecoveryInverseLayout775.values

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseLayout775.excluded
#print axioms ShielddSecurity.RecoveryInverseLayout775.excluded

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseLayout775.bounds
#print axioms ShielddSecurity.RecoveryInverseLayout775.bounds

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseLayout775.alternatives
#print axioms ShielddSecurity.RecoveryInverseLayout775.alternatives
