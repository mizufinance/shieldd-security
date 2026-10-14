import ShielddSecurity.MapSelected709
import ShielddSecurity.MapCofactorArithmetic711
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapCofactorAdapter712
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01

structure Layout where
  x : Linear
  y : Linear
  hint : Nat
  start : Nat

def plus (l : Layout) : Linear := [(copy,1),(l.start+2,(coefficientNat:Int))]
def minus (l : Layout) : Linear := [(copy,1),(l.start+2,-(coefficientNat:Int))]
def offset : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 6 | 5 => 8
  | 6 => 10 | 7 => 12 | 8 => 14 | 9 => 16 | 10 => 18 | _ => 0

def left (l : Layout) : Nat → Linear
  | 0 => l.x | 1 => l.y | 2 => [(l.start,1)] | 3 => plus l | 4 => [(l.hint,1)]
  | 5 => l.x | 6 => l.y | 7 => [(l.start+8,1),(l.start+10,1)]
  | 8 => [(l.start+12,1)] | 9 => [(l.start+1,1),(l.start,1)]
  | 10 => [(l.start+16,1)] | _ => []

def right (l : Layout) : Nat → Linear
  | 0 => l.x | 1 => l.y | 2 => [(l.start+1,1)] | 3 => minus l | 4 => [(l.start+4,1)]
  | 5 => l.y | 6 => l.x | 7 => minus l | 8 => [(l.hint,1)]
  | 9 => plus l | 10 => [(l.hint,1)] | _ => []

def Valid (l : Layout) (index : Nat) (e : MapArithmeticAdapter704.Entry) : Prop :=
  index<11 ∧ e.square=decide (index<2) ∧ canonical p e.left=canonical p (left l index) ∧
  canonical p e.right=canonical p (right l index) ∧ canonical p e.output=canonical p [(l.start+offset index,1)]
noncomputable instance validDecidable (l : Layout) (index : Nat) (e : MapArithmeticAdapter704.Entry) : Decidable (Valid l index e) := by
  unfold Valid
  infer_instance
noncomputable def check (l : Layout) (index : Nat) (e : MapArithmeticAdapter704.Entry) : Bool := decide (Valid l index e)

def Equation (rho : Nat → F) (l : Layout) (index : Nat) : Prop :=
  rho (l.start+offset index)=if index<2 then eval rho (left l index)*eval rho (left l index)
    else eval rho (left l index)*eval rho (right l index)

theorem equation (l : Layout) (index : Nat) (e : MapArithmeticAdapter704.Entry)
    (shape : check l index e=true) (checked : MapArithmeticAdapter704.check e=true)
    (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : Equation rho l index := by
  rcases (of_decide_eq_true shape : Valid l index e) with ⟨_,square,x,y,out⟩
  have raw := MapArithmeticAdapter704.equation e checked rho arithmetic
  have result : eval rho e.output=rho (l.start+offset index) := by
    rw [canonical_equal rho _ _ out]
    simp only [eval,Int.cast_one,one_mul,add_zero]
  rw [result,square,canonical_equal rho _ _ x,canonical_equal rho _ _ y] at raw
  simpa only [Equation,decide_eq_true_eq] using raw

def point (rho : Nat → F) (l : Layout) : Group.Point F := ⟨eval rho l.x,eval rho l.y⟩

theorem local_equations (rho : Nat → F) (l : Layout) (one : rho copy=1)
    (equations : ∀ index<11, Equation rho l index) :
    MapCofactorArithmetic711.Equations coefficient (point rho l) (rho l.hint) (fun i => rho (l.start+i)) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [Equation,offset,left,right,plus,minus,point,eval,one,coefficient,sub_eq_add_neg] using equations 0 (by decide)
  · simpa [Equation,offset,left,right,plus,minus,point,eval,one,coefficient,sub_eq_add_neg] using equations 1 (by decide)
  · simpa [Equation,offset,left,right,plus,minus,point,eval,one,coefficient,sub_eq_add_neg] using equations 2 (by decide)
  · simpa [Equation,offset,left,right,plus,minus,point,eval,one,coefficient,sub_eq_add_neg] using equations 3 (by decide)
  · simpa [Equation,offset,left,right,plus,minus,point,eval,one,coefficient,sub_eq_add_neg] using equations 4 (by decide)
  · simpa [Equation,offset,left,right,plus,minus,point,eval,one,coefficient,sub_eq_add_neg] using equations 5 (by decide)
  · simpa [Equation,offset,left,right,plus,minus,point,eval,one,coefficient,sub_eq_add_neg] using equations 6 (by decide)
  · simpa [Equation,offset,left,right,plus,minus,point,eval,one,coefficient,sub_eq_add_neg] using equations 7 (by decide)
  · simpa [Equation,offset,left,right,plus,minus,point,eval,one,coefficient,sub_eq_add_neg] using equations 8 (by decide)
  · simpa [Equation,offset,left,right,plus,minus,point,eval,one,coefficient,sub_eq_add_neg] using equations 9 (by decide)
  · simpa [Equation,offset,left,right,plus,minus,point,eval,one,coefficient,sub_eq_add_neg] using equations 10 (by decide)

theorem complete (rho : Nat → F) (l : Layout) (one : rho copy=1)
    (equations : ∀ index<11, Equation rho l index)
    (valid : Group.OnCurve coefficient (point rho l))
    (hint : rho l.hint=(CompilerSubgroupArithmetic79.inverseProduct coefficient (point rho l))⁻¹) :
    rho (l.start+6)=1 ∧ Group.Point.mk (rho (l.start+14)) (rho (l.start+18))=Group.affineAdd coefficient (point rho l) (point rho l) := by
  have factors := Group.denominators_nonzero coefficient imaginary coefficient_no_unit_square imaginary_square (point rho l) (point rho l) valid valid
  exact MapCofactorArithmetic711.complete coefficient (point rho l) (rho l.hint) (fun i => rho (l.start+i))
    (local_equations rho l one equations) hint (mul_ne_zero factors.1 factors.2)
end ShielddSecurity.MapCofactorAdapter712

set_option pp.all true in
#check @ShielddSecurity.MapCofactorAdapter712.equation
#print axioms ShielddSecurity.MapCofactorAdapter712.equation

set_option pp.all true in
#check @ShielddSecurity.MapCofactorAdapter712.local_equations
#print axioms ShielddSecurity.MapCofactorAdapter712.local_equations

set_option pp.all true in
#check @ShielddSecurity.MapCofactorAdapter712.complete
#print axioms ShielddSecurity.MapCofactorAdapter712.complete
