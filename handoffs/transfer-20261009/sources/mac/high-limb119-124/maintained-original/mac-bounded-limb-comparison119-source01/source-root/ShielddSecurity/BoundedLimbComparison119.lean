import ShielddSecurity.BinaryComparison100
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BoundedLimbComparison119
open Compiler
variable {F : Type} [Field F]
def borrow (a b : Nat) : Bool := decide (b<a)
def difference (width a b : Nat) : Nat := if a≤b then b-a else 2^width+b-a
theorem difference_bound (width a b : Nat) (left : a<2^width) (right : b<2^width) :
    difference width a b<2^width := by
  unfold difference
  split <;> omega
theorem balance (width a b : Nat) (left : a<2^width) :
    difference width a b+a=b+(if a≤b then 0 else 2^width) := by
  unfold difference
  split <;> omega
theorem borrow_boolean (a b : Nat) :
    Square (BinaryComparison100.bit (F:=F) (borrow a b)) (BinaryComparison100.bit (F:=F) (borrow a b)) := by
  unfold borrow
  by_cases h : b<a <;> simp [h,BinaryComparison100.bit,Square]
theorem field_balance (width a b : Nat) (left : a<2^width) :
    (b:F)-(a:F)=(difference width a b:F)-
      BinaryComparison100.bit (F:=F) (borrow a b)*(2^width:F) := by
  have h:=congrArg (fun n : Nat => (n:F)) (balance width a b left)
  simp only [Nat.cast_add] at h
  by_cases before : a≤b
  · simp only [if_pos before,Nat.cast_zero,add_zero] at h
    have noBorrow : ¬b<a := by omega
    simp only [borrow,decide_eq_false_iff_not.mpr noBorrow,BinaryComparison100.bit,Bool.false_eq_true,
      if_false,zero_mul,sub_zero]
    linear_combination h
  · simp only [if_neg before] at h
    have yesBorrow : b<a := by omega
    simp only [borrow,decide_eq_true_eq.mpr yesBorrow,BinaryComparison100.bit,if_true,one_mul]
    linear_combination h
def result (a b : Nat) : F := 1-BinaryComparison100.bit (F:=F) (borrow a b)
theorem result_exact (a b : Nat) : result (F:=F) a b=if a≤b then 1 else 0 := by
  by_cases before : a≤b
  · have noBorrow : ¬b<a := by omega
    simp [result,borrow,noBorrow,BinaryComparison100.bit,before]
  · have yesBorrow : b<a := by omega
    simp [result,borrow,yesBorrow,BinaryComparison100.bit,before]
end ShielddSecurity.BoundedLimbComparison119

set_option pp.all true in
#check @ShielddSecurity.BoundedLimbComparison119.borrow
#print axioms ShielddSecurity.BoundedLimbComparison119.borrow
set_option pp.all true in
#check @ShielddSecurity.BoundedLimbComparison119.difference
#print axioms ShielddSecurity.BoundedLimbComparison119.difference
set_option pp.all true in
#check @ShielddSecurity.BoundedLimbComparison119.difference_bound
#print axioms ShielddSecurity.BoundedLimbComparison119.difference_bound
set_option pp.all true in
#check @ShielddSecurity.BoundedLimbComparison119.balance
#print axioms ShielddSecurity.BoundedLimbComparison119.balance
set_option pp.all true in
#check @ShielddSecurity.BoundedLimbComparison119.borrow_boolean
#print axioms ShielddSecurity.BoundedLimbComparison119.borrow_boolean
set_option pp.all true in
#check @ShielddSecurity.BoundedLimbComparison119.field_balance
#print axioms ShielddSecurity.BoundedLimbComparison119.field_balance
set_option pp.all true in
#check @ShielddSecurity.BoundedLimbComparison119.result
#print axioms ShielddSecurity.BoundedLimbComparison119.result
set_option pp.all true in
#check @ShielddSecurity.BoundedLimbComparison119.result_exact
#print axioms ShielddSecurity.BoundedLimbComparison119.result_exact
