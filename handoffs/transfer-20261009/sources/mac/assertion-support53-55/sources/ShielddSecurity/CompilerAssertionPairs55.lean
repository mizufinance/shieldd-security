import ShielddSecurity.CompilerAssertionBlock51
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerAssertionPairs55
open CompilerAssertionBlock51
def checkPairs (p copy : Nat) : List Row → List (Bool × Recipe) → Bool
  | [],[] => true
  | row::rows,hint::hints => checkRow p copy row hint && checkPairs p copy rows hints
  | _,_ => false
theorem checked_at (p copy : Nat) (actual : List Row) (hints : List (Bool × Recipe))
    (checked : checkPairs p copy actual hints=true) (index : Nat) (bound : index<actual.length) :
    ∃ row hint, actual[index]?=some row ∧ hints[index]?=some hint ∧ checkRow p copy row hint=true := by
  induction actual generalizing hints index with
  | nil => simp only [List.length_nil] at bound; omega
  | cons row rows ih =>
    cases hints with
    | nil => simp only [checkPairs,Bool.false_eq_true] at checked
    | cons hint hints =>
      have both:=Bool.and_eq_true_iff.mp checked
      cases index with
      | zero => exact ⟨row,hint,rfl,rfl,both.1⟩
      | succ index =>
        simpa only [List.getElem?_cons_succ] using ih hints both.2 index (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using bound)
noncomputable def leaf (p copy length : Nat) (actual : List Row) (hints : List (Bool × Recipe))
    (count : actual.length=length) (checked : checkPairs p copy actual hints=true) :
    CompilerAssertionBlock51.Block p copy length where
  actual := fun index => actual[index]?
  recipe := fun index => hints[index]?
  exact_checked := fun index bound => checked_at p copy actual hints checked index (by omega)
theorem checkPairs_append (p copy : Nat) (left right : List Row) (leftHints rightHints : List (Bool × Recipe))
    (same : left.length=leftHints.length) :
    checkPairs p copy (left++right) (leftHints++rightHints)=
      (checkPairs p copy left leftHints && checkPairs p copy right rightHints) := by
  induction left generalizing leftHints with
  | nil =>
    have empty:leftHints=[]:=List.eq_nil_of_length_eq_zero same.symm
    subst leftHints
    rfl
  | cons row rows ih =>
    cases leftHints with
    | nil => simp only [List.length_cons,List.length_nil] at same; omega
    | cons hint hints =>
      have tailSame:rows.length=hints.length:=Nat.succ.inj same
      simp only [List.cons_append,checkPairs,ih hints tailSame,Bool.and_assoc]
theorem old_check (p copy : Nat) (actual : List Row) (hints : List (Bool × Recipe))
    (checked : checkPairs p copy actual hints=true) :
    CompilerAssertionBlock51.checkList p copy actual hints=true := by
  apply List.all_eq_true.mpr
  intro index member
  obtain ⟨row,hint,foundRow,foundHint,valid⟩:=checked_at p copy actual hints checked index (List.mem_range.mp member)
  simpa only [foundRow,foundHint] using valid
end ShielddSecurity.CompilerAssertionPairs55

set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionPairs55.checkPairs
#print axioms ShielddSecurity.CompilerAssertionPairs55.checkPairs
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionPairs55.checked_at
#print axioms ShielddSecurity.CompilerAssertionPairs55.checked_at
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionPairs55.leaf
#print axioms ShielddSecurity.CompilerAssertionPairs55.leaf
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionPairs55.checkPairs_append
#print axioms ShielddSecurity.CompilerAssertionPairs55.checkPairs_append
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionPairs55.old_check
#print axioms ShielddSecurity.CompilerAssertionPairs55.old_check
