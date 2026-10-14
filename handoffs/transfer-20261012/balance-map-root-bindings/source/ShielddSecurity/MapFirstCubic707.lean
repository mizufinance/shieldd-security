import ShielddSecurity.MapLiterals706
import ShielddSecurity.MapArithmeticCapture705B00
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapFirstCubic707
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01
open BalanceMapParameters699 MapLiterals706
open MapArithmeticCapture705B00

def hashInput : Linear := entry0.right
def xInput : Linear := [(20934,negativeC1Literal)]

theorem q_value (rho : Nat → F) (u : F)
    (input : eval rho hashInput=u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 189643=5*u*u := by
  have raw := MapArithmeticAdapter704.equation entry0 checked0 rho arithmetic
  change eval rho entry0.output=eval rho entry0.left*eval rho entry0.right at raw
  have out : eval rho entry0.output=rho 189643 := by simp only [entry0,eval,Int.cast_one,one_mul,add_zero]
  have scaled : canonical p entry0.left=canonical p (scaleLinear 5 hashInput) := by decide +kernel
  have left : eval rho entry0.left=5*u := by
    rw [canonical_equal rho _ _ scaled,eval_scale,input]
    rfl
  rw [out,left] at raw
  exact raw.trans (congrArg (fun v : F => 5*u*v) input)

theorem x_value (rho : Nat → F) (u : F)
    (inverse : rho 20934=(sourceDenominator u)⁻¹) : eval rho xInput=sourceFirstX u := by
  change (negativeC1Literal:F)*rho 20934+0=sourceFirstX u
  rw [add_zero,negative_c1_meaning,inverse]
  rfl

theorem initial_inverse (rho : Nat → F) (u : F)
    (one : rho copy=1) (input : eval rho hashInput=u)
    (inverse : rho 20934=(sourceDenominator u)⁻¹)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 189645=1 := by
  have raw := MapArithmeticAdapter704.equation entry1 checked1 rho arithmetic
  change eval rho entry1.output=eval rho entry1.left*eval rho entry1.right at raw
  have out : eval rho entry1.output=rho 189645 := by simp only [entry1,eval,Int.cast_one,one_mul,add_zero]
  have left : eval rho entry1.left=(sourceDenominator u)⁻¹ := by
    simpa only [entry1,eval,Int.cast_one,one_mul,add_zero] using inverse
  have right : eval rho entry1.right=sourceDenominator u := by
    simp only [entry1,eval,Int.cast_one,one_mul,add_zero]
    change rho 189643+rho copy=sourceDenominator u
    rw [q_value rho u input arithmetic,one]
    unfold sourceDenominator
    ring
  rw [out,left,right] at raw
  exact raw.trans (inv_mul_cancel₀ (actual_elligator_denominator_is_nonzero u))

theorem first_cubic (rho : Nat → F) (u : F)
    (one : rho copy=1) (inverse : rho 20934=(sourceDenominator u)⁻¹)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 189649=sourceFirstCubic u := by
  have x := x_value rho u inverse
  have first := MapArithmeticAdapter704.equation entry2 checked2 rho arithmetic
  change eval rho entry2.output=eval rho entry2.left*eval rho entry2.right at first
  have firstOut : eval rho entry2.output=rho 189647 := by simp only [entry2,eval,Int.cast_one,one_mul,add_zero]
  have firstLeft : eval rho entry2.left=sourceFirstX u+sourceC1 := by
    change (negativeC1Literal:F)*rho 20934+((c1Literal:F)*rho copy+0)=sourceFirstX u+sourceC1
    rw [one,mul_one,add_zero,c1_meaning]
    exact congrArg (fun v : F => v+sourceC1) (by simpa only [xInput,eval,add_zero] using x)
  have firstRight : eval rho entry2.right=sourceFirstX u := x
  rw [firstOut,firstLeft,firstRight] at first
  have second := MapArithmeticAdapter704.equation entry3 checked3 rho arithmetic
  change eval rho entry3.output=eval rho entry3.left*eval rho entry3.right at second
  have secondOut : eval rho entry3.output=rho 189649 := by simp only [entry3,eval,Int.cast_one,one_mul,add_zero]
  have secondLeft : eval rho entry3.left=rho 189647+sourceC2 := by
    simp only [entry3,eval,Int.cast_one,one_mul,add_zero]
    change rho 189647+(c2Literal:F)*rho copy=rho 189647+sourceC2
    rw [one,mul_one,c2_meaning]
  have secondRight : eval rho entry3.right=sourceFirstX u := x
  rw [secondOut,secondLeft,secondRight,first] at second
  exact second
end ShielddSecurity.MapFirstCubic707

set_option pp.all true in
#check @ShielddSecurity.MapFirstCubic707.q_value
#print axioms ShielddSecurity.MapFirstCubic707.q_value

set_option pp.all true in
#check @ShielddSecurity.MapFirstCubic707.x_value
#print axioms ShielddSecurity.MapFirstCubic707.x_value

set_option pp.all true in
#check @ShielddSecurity.MapFirstCubic707.initial_inverse
#print axioms ShielddSecurity.MapFirstCubic707.initial_inverse

set_option pp.all true in
#check @ShielddSecurity.MapFirstCubic707.first_cubic
#print axioms ShielddSecurity.MapFirstCubic707.first_cubic
