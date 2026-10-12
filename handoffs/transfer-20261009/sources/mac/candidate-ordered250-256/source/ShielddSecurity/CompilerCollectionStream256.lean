import ShielddSecurity.CompilerIndexedCopyCollection174
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerCollectionStream256
open Compiler CompilerAssertionBlock51
theorem row_weaken (p copy : Nat) (parent : Nat → Option Row) (length position : Nat) (target : Row)
 (checked : CompilerIndexedCopyCollection174.rowCheck copy parent length position target=true) :
 CompilerIndexedCopyStream171.rowCheck p copy parent length position target=true := by
 cases found:parent position with
 | none => simp only [CompilerIndexedCopyCollection174.rowCheck,found] at checked;contradiction
 | some actual =>
   simp only [CompilerIndexedCopyCollection174.rowCheck,found] at checked
   have facts : position<length ∧collect (unoutline copy actual.a)=collect (unoutline copy target.a) ∧
     collect (unoutline copy actual.b)=collect (unoutline copy target.b) := of_decide_eq_true checked
   simp only [CompilerIndexedCopyStream171.rowCheck,found]
   apply decide_eq_true
   exact ⟨facts.1,congrArg (reduceCoefficients p) facts.2.1,congrArg (reduceCoefficients p) facts.2.2⟩
theorem check_weaken (p copy : Nat) (parent : Nat → Option Row) (length : Nat)
 (indices : List Nat) (targets : List Row)
 (checked : CompilerIndexedCopyCollection174.check copy parent length indices targets=true) :
 CompilerIndexedCopyStream171.check p copy parent length indices targets=true := by
 induction indices generalizing targets with
 | nil =>
   cases targets with
   | nil => rfl
   | cons a rest => simp only [CompilerIndexedCopyCollection174.check] at checked;contradiction
 | cons position indices ih =>
   cases targets with
   | nil => simp only [CompilerIndexedCopyCollection174.check] at checked;contradiction
   | cons target rest =>
     have facts:=Bool.and_eq_true_iff.mp checked
     exact Bool.and_eq_true_iff.mpr ⟨row_weaken p copy parent length position target facts.1,ih rest facts.2⟩
end ShielddSecurity.CompilerCollectionStream256

set_option pp.all true in
#check @ShielddSecurity.CompilerCollectionStream256.row_weaken
#print axioms ShielddSecurity.CompilerCollectionStream256.row_weaken
set_option pp.all true in
#check @ShielddSecurity.CompilerCollectionStream256.check_weaken
#print axioms ShielddSecurity.CompilerCollectionStream256.check_weaken
