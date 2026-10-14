import ShielddSecurity.ComparisonBorrowFrame324
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapWitnessLayout715
-- The choice and zero flags are deliberately excluded: boolean completion writes them.
def values : List Nat := [20934,20936,20937,21194,21195,21196,21197,21198]
def Inside (column : Nat) : Prop := column∈values
def outside (column : Nat) : Bool := decide (column∉values)
theorem excluded (column : Nat) (checked : outside column=true) (inside : Inside column) : False :=
  (of_decide_eq_true checked) inside
theorem bounds (column : Nat) (inside : Inside column) : 20934≤column ∧ column<21199 := by
  have checked : values.all (fun n => decide (20934≤n ∧ n<21199))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked column inside)
end ShielddSecurity.MapWitnessLayout715

set_option pp.all true in
#check @ShielddSecurity.MapWitnessLayout715.values
#print axioms ShielddSecurity.MapWitnessLayout715.values

set_option pp.all true in
#check @ShielddSecurity.MapWitnessLayout715.excluded
#print axioms ShielddSecurity.MapWitnessLayout715.excluded

set_option pp.all true in
#check @ShielddSecurity.MapWitnessLayout715.bounds
#print axioms ShielddSecurity.MapWitnessLayout715.bounds
