import ShielddSecurity.ComparisonBorrowFrame324
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SemanticCopiesLayout795
-- The recovery commitment and encryption timestamp copies is outside all Boolean and word windows.
def values : List Nat := [4790,4921,6195,6325,8541]
def Inside (column : Nat) : Prop := column∈values
def outside (column : Nat) : Bool := decide (column∉values)
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False :=
  (of_decide_eq_true checked) inside
theorem bounds (column : Nat) (inside : Inside column) : 4790≤column ∧ column<8542 := by
  have checked : values.all (fun n => decide (4790≤n ∧ n<8542))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked column inside)
theorem alternatives (column : Nat) (inside : Inside column) : column=4790 ∨ column=4921 ∨ column=6195 ∨ column=6325 ∨ column=8541 := by
  simpa only [Inside,values,List.mem_cons,List.not_mem_nil,or_false] using inside
end ShielddSecurity.SemanticCopiesLayout795

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesLayout795.values
#print axioms ShielddSecurity.SemanticCopiesLayout795.values

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesLayout795.excluded
#print axioms ShielddSecurity.SemanticCopiesLayout795.excluded

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesLayout795.bounds
#print axioms ShielddSecurity.SemanticCopiesLayout795.bounds

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesLayout795.alternatives
#print axioms ShielddSecurity.SemanticCopiesLayout795.alternatives
