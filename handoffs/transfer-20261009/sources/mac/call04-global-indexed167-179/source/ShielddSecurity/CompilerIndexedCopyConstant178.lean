import ShielddSecurity.CompilerIndexedCopySelection166
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerIndexedCopyConstant178
open Compiler CompilerAssertionBlock51
-- Linear pass: move only zero/copy coefficients; preserve other term order.
def pack (copy : Nat) : Linear → Int × Linear
  | [] => (0,[])
  | (column,coefficient)::rest =>
    let tail:=pack copy rest
    if column=0 ∨ column=copy then (coefficient+tail.1,tail.2)
    else (tail.1,(column,coefficient)::tail.2)
variable {F : Type} [Field F]
theorem eval_pack (copy : Nat) (xs : Linear) (rho : Nat → F) (linked : rho copy=rho 0) :
    eval rho xs=((pack copy xs).1 : F)*rho 0+eval rho (pack copy xs).2 := by
  induction xs with
  | nil => simp [pack,eval]
  | cons term rest ih =>
    rcases term with ⟨column,coefficient⟩
    by_cases constant : column=0 ∨ column=copy
    · have equal : rho column=rho 0 := by
        rcases constant with zero|copied
        · rw [zero]
        · rw [copied,linked]
      simp only [pack,if_pos constant,eval,Int.cast_add]
      rw [equal,ih]
      ring
    · simp only [pack,if_neg constant,eval]
      rw [ih]
      ring
def rowCheck (copy : Nat) (parent : Nat → Option Row) (fullLength position : Nat) (target : Row) : Bool :=
  match parent position with
  | some actual => decide (position<fullLength ∧
      pack copy actual.a=pack copy target.a ∧
      pack copy actual.b=pack copy target.b)
  | none => false
def check (copy : Nat) (parent : Nat → Option Row) (fullLength : Nat) : List Nat → List Row → Bool
  | [],[] => true
  | position::indices,target::targets => rowCheck copy parent fullLength position target && check copy parent fullLength indices targets
  | _,_ => false
theorem row_sound (copy : Nat) (parent : Nat → Option Row) (fullLength position : Nat) (target : Row)
    (checked : rowCheck copy parent fullLength position target=true) (rho : Nat → F)
    (linked : rho copy=rho 0) (satisfied : SatisfiesAt rho parent fullLength) : Satisfies rho [target] := by
  cases actualFound : parent position with
  | none => simp only [rowCheck,actualFound] at checked;contradiction
  | some actual =>
    simp only [rowCheck,actualFound] at checked
    have facts : position<fullLength ∧
        pack copy actual.a=pack copy target.a ∧
        pack copy actual.b=pack copy target.b := of_decide_eq_true checked
    have row:=satisfied position facts.1 actual actualFound
    have left : eval rho actual.a=eval rho target.a := by
      rw [eval_pack copy actual.a rho linked,eval_pack copy target.a rho linked,facts.2.1]
    have right : eval rho actual.b=eval rho target.b := by
      rw [eval_pack copy actual.b rho linked,eval_pack copy target.b rho linked,facts.2.2]
    rw [left,right] at row
    intro selected member
    have same:=List.mem_singleton.mp member
    subst selected
    exact row
theorem sound (copy : Nat) (parent : Nat → Option Row) (fullLength : Nat)
    (indices : List Nat) (targets : List Row) (checked : check copy parent fullLength indices targets=true)
    (rho : Nat → F) (linked : rho copy=rho 0) (satisfied : SatisfiesAt rho parent fullLength) :
    Satisfies rho targets := by
  induction indices generalizing targets with
  | nil =>
    cases targets with
    | nil => intro row member;cases member
    | cons target rest => simp only [check] at checked;contradiction
  | cons position indices ih =>
    cases targets with
    | nil => intro row member;cases member
    | cons target rest =>
      have checks:=Bool.and_eq_true_iff.mp checked
      have first:=row_sound copy parent fullLength position target checks.1 rho linked satisfied
      have later:=ih rest checks.2
      intro row member
      rcases List.mem_cons.mp member with equal|member
      · subst row;exact first target (List.mem_singleton_self target)
      · exact later row member
end ShielddSecurity.CompilerIndexedCopyConstant178

set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedCopyConstant178.pack
#print axioms ShielddSecurity.CompilerIndexedCopyConstant178.pack
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedCopyConstant178.eval_pack
#print axioms ShielddSecurity.CompilerIndexedCopyConstant178.eval_pack
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedCopyConstant178.rowCheck
#print axioms ShielddSecurity.CompilerIndexedCopyConstant178.rowCheck
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedCopyConstant178.check
#print axioms ShielddSecurity.CompilerIndexedCopyConstant178.check
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedCopyConstant178.row_sound
#print axioms ShielddSecurity.CompilerIndexedCopyConstant178.row_sound
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedCopyConstant178.sound
#print axioms ShielddSecurity.CompilerIndexedCopyConstant178.sound
