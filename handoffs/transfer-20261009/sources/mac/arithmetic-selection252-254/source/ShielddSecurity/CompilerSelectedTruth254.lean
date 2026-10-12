import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerSelectedTruth254
open Compiler CompilerAssertionBlock51
variable {F : Type} [Field F] {p copy : Nat} [CharP F p]
theorem row_selected (parent : Nat → Option Row) (fullLength position : Nat) (target : Row)
 (checked : CompilerIndexedCopyStream171.rowCheck p copy parent fullLength position target=true) (rho : Nat → F)
 (linked : rho copy=rho 0)
 (truth : ∀ actual,parent position=some actual → Square (eval rho actual.a) (eval rho actual.b)) :
 Satisfies rho [target] := by
 cases actualFound:parent position with
 | none => simp only [CompilerIndexedCopyStream171.rowCheck,actualFound] at checked;contradiction
 | some actual =>
   simp only [CompilerIndexedCopyStream171.rowCheck,actualFound] at checked
   have facts : position<fullLength ∧
     canonical p (unoutline copy actual.a)=canonical p (unoutline copy target.a) ∧
     canonical p (unoutline copy actual.b)=canonical p (unoutline copy target.b) := of_decide_eq_true checked
   have row:=truth actual actualFound
   have left : eval rho actual.a=eval rho target.a :=
     (eval_unoutline rho copy _ linked).symm.trans
       ((canonical_equal rho _ _ facts.2.1).trans (eval_unoutline rho copy _ linked))
   have right : eval rho actual.b=eval rho target.b :=
     (eval_unoutline rho copy _ linked).symm.trans
       ((canonical_equal rho _ _ facts.2.2).trans (eval_unoutline rho copy _ linked))
   rw [left,right] at row
   intro selected member
   have same:=List.mem_singleton.mp member
   subst selected
   exact row
theorem selected_sound (parent : Nat → Option Row) (fullLength : Nat)
 (indices : List Nat) (targets : List Row) (checked : CompilerIndexedCopyStream171.check p copy parent fullLength indices targets=true)
 (rho : Nat → F) (linked : rho copy=rho 0)
 (truth : ∀ position∈indices,∀ actual,parent position=some actual → Square (eval rho actual.a) (eval rho actual.b)) :
 Satisfies rho targets := by
 induction indices generalizing targets with
 | nil =>
   cases targets with
   | nil => intro row member;cases member
   | cons target rest => simp only [CompilerIndexedCopyStream171.check] at checked;contradiction
 | cons position indices ih =>
   cases targets with
   | nil => intro row member;cases member
   | cons target rest =>
     have checks:=Bool.and_eq_true_iff.mp checked
     have first:=row_selected parent fullLength position target checks.1 rho linked
       (truth position (List.mem_cons_self ..))
     have later:=ih rest checks.2 (fun i h => truth i (List.mem_cons_of_mem _ h))
     intro row member
     rcases List.mem_cons.mp member with equal|member
     · subst row;exact first target (List.mem_singleton_self target)
     · exact later row member
end ShielddSecurity.CompilerSelectedTruth254

set_option pp.all true in
#check @ShielddSecurity.CompilerSelectedTruth254.row_selected
#print axioms ShielddSecurity.CompilerSelectedTruth254.row_selected
set_option pp.all true in
#check @ShielddSecurity.CompilerSelectedTruth254.selected_sound
#print axioms ShielddSecurity.CompilerSelectedTruth254.selected_sound
