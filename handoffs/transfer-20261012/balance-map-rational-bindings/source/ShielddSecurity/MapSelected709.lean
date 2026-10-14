import ShielddSecurity.MapRootRows708
import ShielddSecurity.MapArithmeticCapture705B02
import ShielddSecurity.BalanceMapPoint701
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapSelected709
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01
open BalanceMapParameters699 MapLiterals706 MapFirstCubic707

theorem mul_output (e : MapArithmeticAdapter704.Entry) (column : Nat)
    (checked : MapArithmeticAdapter704.check e=true) (plain : e.square=false) (slot : e.output=[(column,1)])
    (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (left right : F) (lhs : eval rho e.left=left) (rhs : eval rho e.right=right) : rho column=left*right := by
  have raw := MapArithmeticAdapter704.equation e checked rho arithmetic
  have out : eval rho e.output=rho column := by rw [slot];simp only [eval,Int.cast_one,one_mul,add_zero]
  rw [out,plain] at raw
  simpa only [Bool.false_eq_true,if_false,lhs,rhs] using raw

def alternateInput : Linear := [(20934,c1Literal),(copy,negativeC1Literal)]
def selectedInput : Linear := alternateInput++[(189655,1)]
noncomputable def sInput : Linear := MapArithmeticCapture705B01.entry6.right
noncomputable def plusInput : Linear := MapArithmeticCapture705B01.entry1.left
noncomputable def tInput : Linear := MapArithmeticCapture705B01.entry1.right
noncomputable def minusInput : Linear := MapArithmeticCapture705B02.entry1.right

theorem alternate_value (rho : Nat → F) (u : F) (one : rho copy=1)
    (inverse : rho 20934=(sourceDenominator u)⁻¹) : eval rho alternateInput= -sourceFirstX u-sourceC1 := by
  have shape : canonical p alternateInput=canonical p (subtract [] (xInput++[(copy,(c1Literal:Int))])) := by decide +kernel
  rw [canonical_equal rho _ _ shape,eval_subtract,eval_append,x_value rho u inverse]
  have c1 : eval rho [(copy,c1Literal)]=sourceC1 := by
    change (c1Literal:F)*rho copy+0=sourceC1
    rw [one,mul_one,add_zero,c1_meaning]
  rw [c1]
  change (0:F)-(sourceFirstX u+sourceC1)= -sourceFirstX u-sourceC1
  ring

theorem selected_value (rho : Nat → F) (u : F) (one : rho copy=1)
    (inverse : rho 20934=(sourceDenominator u)⁻¹)
    (flag : rho 20935=if BalanceMapRoots700.choice u then 1 else 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho selectedInput=if BalanceMapRoots700.choice u then sourceFirstX u else -sourceFirstX u-sourceC1 := by
  have shape : canonical p MapArithmeticCapture705B00.entry6.right=canonical p (subtract xInput alternateInput) := by decide +kernel
  have lhs : eval rho MapArithmeticCapture705B00.entry6.left=if BalanceMapRoots700.choice u then 1 else 0 := by
    simpa only [MapArithmeticCapture705B00.entry6,eval,Int.cast_one,one_mul,add_zero] using flag
  have rhs : eval rho MapArithmeticCapture705B00.entry6.right=sourceFirstX u-(-sourceFirstX u-sourceC1) := by
    rw [canonical_equal rho _ _ shape,eval_subtract,x_value rho u inverse,alternate_value rho u one inverse]
  have gate := mul_output MapArithmeticCapture705B00.entry6 189655 MapArithmeticCapture705B00.checked6 rfl rfl rho arithmetic _ _ lhs rhs
  rw [selectedInput,eval_append,alternate_value rho u one inverse]
  simp only [eval,Int.cast_one,one_mul,add_zero]
  cases h : BalanceMapRoots700.choice u <;> simp only [h,Bool.false_eq_true,if_false,if_true,zero_mul,one_mul] at gate ⊢ <;> linear_combination gate

theorem s_value (rho : Nat → F) (u : F) (one : rho copy=1)
    (inverse : rho 20934=(sourceDenominator u)⁻¹)
    (flag : rho 20935=if BalanceMapRoots700.choice u then 1 else 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : eval rho sInput=BalanceMapPoint701.s u := by
  have shape : canonical p sInput=canonical p (scaleLinear kLiteral selectedInput) := by decide +kernel
  rw [canonical_equal rho _ _ shape,eval_scale,selected_value rho u one inverse flag arithmetic]
  rw [Int.cast_natCast,k_meaning]
  unfold BalanceMapPoint701.s
  ring

theorem t_value (rho : Nat → F) (u : F) (selected : rho 20937=BalanceMapRoots700.selectedRoot u) :
    eval rho tInput=BalanceMapPoint701.t u := by
  change (kLiteral:F)*rho 20937+0=BalanceMapPoint701.t u
  rw [add_zero,k_meaning,selected]
  unfold BalanceMapPoint701.t
  ring

theorem plus_value (rho : Nat → F) (u : F) (one : rho copy=1)
    (s : eval rho sInput=BalanceMapPoint701.s u) : eval rho plusInput=BalanceMapPoint701.s u+1 := by
  have shape : canonical p plusInput=canonical p (sInput++[(copy,1)]) := by decide +kernel
  rw [canonical_equal rho _ _ shape,eval_append,s]
  simp only [eval,Int.cast_one,one_mul,add_zero,one]

theorem minus_value (rho : Nat → F) (u : F) (one : rho copy=1)
    (s : eval rho sInput=BalanceMapPoint701.s u) : eval rho minusInput=BalanceMapPoint701.s u-1 := by
  have shape : canonical p minusInput=canonical p (subtract sInput [(copy,1)]) := by decide +kernel
  rw [canonical_equal rho _ _ shape,eval_subtract,s]
  simp only [eval,Int.cast_one,one_mul,add_zero,one]
end ShielddSecurity.MapSelected709

set_option pp.all true in
#check @ShielddSecurity.MapSelected709.mul_output
#print axioms ShielddSecurity.MapSelected709.mul_output

set_option pp.all true in
#check @ShielddSecurity.MapSelected709.alternate_value
#print axioms ShielddSecurity.MapSelected709.alternate_value

set_option pp.all true in
#check @ShielddSecurity.MapSelected709.selected_value
#print axioms ShielddSecurity.MapSelected709.selected_value

set_option pp.all true in
#check @ShielddSecurity.MapSelected709.s_value
#print axioms ShielddSecurity.MapSelected709.s_value

set_option pp.all true in
#check @ShielddSecurity.MapSelected709.t_value
#print axioms ShielddSecurity.MapSelected709.t_value

set_option pp.all true in
#check @ShielddSecurity.MapSelected709.plus_value
#print axioms ShielddSecurity.MapSelected709.plus_value

set_option pp.all true in
#check @ShielddSecurity.MapSelected709.minus_value
#print axioms ShielddSecurity.MapSelected709.minus_value
