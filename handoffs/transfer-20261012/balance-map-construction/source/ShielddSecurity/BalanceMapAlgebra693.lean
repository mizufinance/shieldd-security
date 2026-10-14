import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.BalanceMapAlgebra693

-- A generic algebraic implication only: the captured map must separately supply
-- the cubic equation and show that its output is this rational transformation.
theorem cleared {F : Type} [CommRing F] (A K d s t : F)
    (coefficient : d*K=A-2) (scale : K=-(A+2))
    (cubic : K*t^2=s^3+A*s^2+s) :
    -K*s^2*(s+1)^2+K*t^2*(s-1)^2 =
      K*t^2*(s+1)^2+(d*K)*s^2*(s-1)^2 := by
  apply sub_eq_zero.mp
  calc
    -K*s^2*(s+1)^2+K*t^2*(s-1)^2 -
        (K*t^2*(s+1)^2+(d*K)*s^2*(s-1)^2) =
      -4*s*(K*t^2-(s^3+A*s^2+s)) := by rw [coefficient,scale]; ring
    _ = 0 := by rw [cubic,sub_self,mul_zero]

theorem rational {F : Type} [Field F] (A K d s t : F)
    (coefficient : d*K=A-2) (scale : K=-(A+2))
    (nonzero : K≠0) (denominator : (s+1)*t≠0)
    (cubic : K*t^2=s^3+A*s^2+s) :
    -(s/t)^2+((s-1)/(s+1))^2 = 1+d*(s/t)^2*((s-1)/(s+1))^2 := by
  have ht : t≠0 := (mul_ne_zero_iff.mp denominator).2
  have hs : s+1≠0 := (mul_ne_zero_iff.mp denominator).1
  have equation := cleared A K d s t coefficient scale cubic
  have unscaled : -s^2*(s+1)^2+t^2*(s-1)^2 =
      t^2*(s+1)^2+d*s^2*(s-1)^2 := by
    apply (mul_left_cancel₀ nonzero)
    linear_combination equation
  field_simp [ht,hs]
  linear_combination unscaled

theorem with_identity_branch {F : Type} [Field F] [DecidableEq F] (A K d s t : F)
    (coefficient : d*K=A-2) (scale : K=-(A+2)) (nonzero : K≠0)
    (cubic : K*t^2=s^3+A*s^2+s) :
    let point := if (s+1)*t=0 then ((0:F),(1:F)) else (s/t,(s-1)/(s+1));
    -point.1^2+point.2^2=1+d*point.1^2*point.2^2 := by
  dsimp only
  split_ifs with zero
  · norm_num
  · exact rational A K d s t coefficient scale nonzero zero cubic
end ShielddSecurity.BalanceMapAlgebra693

set_option pp.all true in
#check @ShielddSecurity.BalanceMapAlgebra693.cleared
#print axioms ShielddSecurity.BalanceMapAlgebra693.cleared

set_option pp.all true in
#check @ShielddSecurity.BalanceMapAlgebra693.rational
#print axioms ShielddSecurity.BalanceMapAlgebra693.rational

set_option pp.all true in
#check @ShielddSecurity.BalanceMapAlgebra693.with_identity_branch
#print axioms ShielddSecurity.BalanceMapAlgebra693.with_identity_branch
