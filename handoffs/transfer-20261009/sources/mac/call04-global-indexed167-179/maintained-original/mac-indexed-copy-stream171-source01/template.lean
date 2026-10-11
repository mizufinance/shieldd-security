import ShielddSecurity.CompilerIndexedCopySelection166
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerIndexedCopyStream171
open Compiler CompilerAssertionBlock51
-- Consume both lists once rather than repeatedly rebuilding indexed target prefixes.
def rowCheck (p copy : Nat) (parent : Nat → Option Row) (fullLength position : Nat) (target : Row) : Bool :=
  match parent position with
  | some actual => decide (position<fullLength ∧
      canonical p (unoutline copy actual.a)=canonical p (unoutline copy target.a) ∧
      canonical p (unoutline copy actual.b)=canonical p (unoutline copy target.b))
  | none => false
def check (p copy : Nat) (parent : Nat → Option Row) (fullLength : Nat) : List Nat → List Row → Bool
  | [],[] => true
  | position::indices,target::targets => rowCheck p copy parent fullLength position target && check p copy parent fullLength indices targets
  | _,_ => false
variable {F : Type} [Field F] {p : Nat} [CharP F p]
theorem row_sound (copy : Nat) (parent : Nat → Option Row) (fullLength position : Nat) (target : Row)
    (checked : rowCheck p copy parent fullLength position target=true) (rho : Nat → F)
    (linked : rho copy=rho 0) (satisfied : SatisfiesAt rho parent fullLength) : Satisfies rho [target] := by
  cases actualFound : parent position with
  | none => simp only [rowCheck,actualFound] at checked;contradiction
  | some actual =>
    simp only [rowCheck,actualFound] at checked
    have facts : position<fullLength ∧
        canonical p (unoutline copy actual.a)=canonical p (unoutline copy target.a) ∧
        canonical p (unoutline copy actual.b)=canonical p (unoutline copy target.b) := of_decide_eq_true checked
    have row:=satisfied position facts.1 actual actualFound
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
    intro selected member
    have same:=List.mem_singleton.mp member
    subst selected
    exact row
theorem sound (copy : Nat) (parent : Nat → Option Row) (fullLength : Nat)
    (indices : List Nat) (targets : List Row) (checked : check p copy parent fullLength indices targets=true)
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
end ShielddSecurity.CompilerIndexedCopyStream171
