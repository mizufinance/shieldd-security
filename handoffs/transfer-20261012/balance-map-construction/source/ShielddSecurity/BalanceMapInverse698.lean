import ShielddSecurity.BalanceMapAlgebra693
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.BalanceMapInverse698

-- These are the three source circuit equations for the zero flag and inverse.
theorem constraints {F : Type} [Field F] [DecidableEq F] (denom : F) :
    let zero : F := if denom=0 then 1 else 0;
    denom*denom⁻¹=1-zero ∧ denom*zero=0 ∧ denom⁻¹*zero=0 := by
  by_cases h : denom=0
  · simp [h]
  · simp [h]

theorem coordinates {F : Type} [Field F] [DecidableEq F] (s t : F) :
    let denom := (s+1)*t;
    let zero : F := if denom=0 then 1 else 0;
    (denom⁻¹*(s+1)*s,denom⁻¹*t*(s-1)+zero)=
      if denom=0 then ((0:F),(1:F)) else (s/t,(s-1)/(s+1)) := by
  dsimp only
  by_cases h : (s+1)*t=0
  · simp [h]
  · have ht : t≠0 := (mul_ne_zero_iff.mp h).2
    have hs : s+1≠0 := (mul_ne_zero_iff.mp h).1
    simp only [if_neg h,add_zero]
    apply Prod.ext
    · dsimp only
      field_simp [ht,hs]
    · dsimp only
      field_simp [ht,hs]

theorem circuit_curve {F : Type} [Field F] [DecidableEq F] (A K d s t : F)
    (coefficient : d*K=A-2) (scale : K=-(A+2)) (nonzero : K≠0)
    (cubic : K*t^2=s^3+A*s^2+s) :
    let denom := (s+1)*t;
    let zero : F := if denom=0 then 1 else 0;
    let point := (denom⁻¹*(s+1)*s,denom⁻¹*t*(s-1)+zero);
    -point.1^2+point.2^2=1+d*point.1^2*point.2^2 := by
  change -( ((s+1)*t)⁻¹*(s+1)*s)^2 +
    (((s+1)*t)⁻¹*t*(s-1)+(if (s+1)*t=0 then 1 else 0))^2 = _
  have eqn := congrArg (fun point : F×F =>
    -point.1^2+point.2^2-(1+d*point.1^2*point.2^2)) (coordinates s t)
  have curve := BalanceMapAlgebra693.with_identity_branch A K d s t coefficient scale nonzero cubic
  apply sub_eq_zero.mp
  exact eqn.trans (sub_eq_zero.mpr curve)
end ShielddSecurity.BalanceMapInverse698

set_option pp.all true in
#check @ShielddSecurity.BalanceMapInverse698.constraints
#print axioms ShielddSecurity.BalanceMapInverse698.constraints

set_option pp.all true in
#check @ShielddSecurity.BalanceMapInverse698.coordinates
#print axioms ShielddSecurity.BalanceMapInverse698.coordinates

set_option pp.all true in
#check @ShielddSecurity.BalanceMapInverse698.circuit_curve
#print axioms ShielddSecurity.BalanceMapInverse698.circuit_curve
