import ShielddSecurity.CompilerIndexedCopySelection166
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerIndexedTruth260
open Compiler CompilerAssertionBlock51 CompilerIndexedCopySelection166
variable {F : Type} [Field F] {p : Nat} [CharP F p]
theorem selected_sound (copy : Nat) (parent : Nat → Option Row) (fullLength : Nat)
    (indices : List Nat) (targets : List Row) (checked : check p copy parent fullLength indices targets=true)
    (rho : Nat → F) (linked : rho copy=rho 0) (truth : ∀ position∈indices,∀ actual,parent position=some actual → Square (eval rho actual.a) (eval rho actual.b)) :
    Satisfies rho targets := by
  intro target member
  obtain ⟨index,bound,same⟩:=List.mem_iff_getElem.mp member
  have found : targets[index]?=some target := List.getElem?_eq_some_iff.mpr ⟨bound,same⟩
  have localCheck:=List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 index (List.mem_range.mpr bound)
  rw [found] at localCheck
  cases selected : indices[index]? with
  | none => simp only [selected] at localCheck;contradiction
  | some position =>
    cases actualFound : parent position with
    | none => simp only [selected,actualFound] at localCheck;contradiction
    | some actual =>
      simp only [selected,actualFound] at localCheck
      have facts : position<fullLength ∧
          canonical p (unoutline copy actual.a)=canonical p (unoutline copy target.a) ∧
          canonical p (unoutline copy actual.b)=canonical p (unoutline copy target.b) := of_decide_eq_true localCheck
      have row:=truth position (List.mem_of_getElem? selected) actual actualFound
      have left : eval rho actual.a=eval rho target.a := by
        calc
          eval rho actual.a=eval rho (unoutline copy actual.a) := (eval_unoutline rho copy _ linked).symm
          _=eval rho (unoutline copy target.a) := canonical_equal rho _ _ facts.2.1
          _=eval rho target.a := eval_unoutline rho copy _ linked
      have right : eval rho actual.b=eval rho target.b := by
        calc
          eval rho actual.b=eval rho (unoutline copy actual.b) := (eval_unoutline rho copy _ linked).symm
          _=eval rho (unoutline copy target.b) := canonical_equal rho _ _ facts.2.2
          _=eval rho target.b := eval_unoutline rho copy _ linked
      rw [left,right] at row
      exact row
end ShielddSecurity.CompilerIndexedTruth260

set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedTruth260.selected_sound
#print axioms ShielddSecurity.CompilerIndexedTruth260.selected_sound
