import ShielddSecurity.CompilerIndexedCopyConstant178
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerPackedTruth257
open Compiler CompilerAssertionBlock51 CompilerIndexedCopyConstant178
variable {F : Type} [Field F]
theorem row_selected (copy : Nat) (parent : Nat → Option Row) (fullLength position : Nat) (target : Row)
    (checked : rowCheck copy parent fullLength position target=true) (rho : Nat → F)
    (linked : rho copy=rho 0) (truth : ∀ actual,parent position=some actual → Square (eval rho actual.a) (eval rho actual.b)) : Satisfies rho [target] := by
  cases actualFound : parent position with
  | none => simp only [rowCheck,actualFound] at checked;contradiction
  | some actual =>
    simp only [rowCheck,actualFound] at checked
    have facts : position<fullLength ∧
        pack copy actual.a=pack copy target.a ∧
        pack copy actual.b=pack copy target.b := of_decide_eq_true checked
    have row:=truth actual actualFound
    have left : eval rho actual.a=eval rho target.a := by
      rw [eval_pack copy actual.a rho linked,eval_pack copy target.a rho linked,facts.2.1]
    have right : eval rho actual.b=eval rho target.b := by
      rw [eval_pack copy actual.b rho linked,eval_pack copy target.b rho linked,facts.2.2]
    rw [left,right] at row
    intro selected member
    have same:=List.mem_singleton.mp member
    subst selected
    exact row
theorem selected_sound (copy : Nat) (parent : Nat → Option Row) (fullLength : Nat)
    (indices : List Nat) (targets : List Row) (checked : check copy parent fullLength indices targets=true)
    (rho : Nat → F) (linked : rho copy=rho 0) (truth : ∀ position∈indices,∀ actual,parent position=some actual → Square (eval rho actual.a) (eval rho actual.b)) :
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
      have first:=row_selected copy parent fullLength position target checks.1 rho linked (truth position (List.mem_cons_self ..))
      have later:=ih rest checks.2 (fun i h => truth i (List.mem_cons_of_mem _ h))
      intro row member
      rcases List.mem_cons.mp member with equal|member
      · subst row;exact first target (List.mem_singleton_self target)
      · exact later row member
end ShielddSecurity.CompilerPackedTruth257

set_option pp.all true in
#check @ShielddSecurity.CompilerPackedTruth257.row_selected
#print axioms ShielddSecurity.CompilerPackedTruth257.row_selected
set_option pp.all true in
#check @ShielddSecurity.CompilerPackedTruth257.selected_sound
#print axioms ShielddSecurity.CompilerPackedTruth257.selected_sound
