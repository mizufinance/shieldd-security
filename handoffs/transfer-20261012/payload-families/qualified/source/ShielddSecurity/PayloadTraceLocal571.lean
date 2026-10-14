import ShielddSecurity.AuthorizationTraceLocal453
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadTraceLocal571
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open AuthorizationTraceSeed451
attribute [local irreducible] model windowAt

theorem component (base : curve.Point) (scalar window part : Nat) (lower : 1≤window) (small : part<3) :
    hintPoint base scalar (3*window+part)=AuthorizationTraceSeed451.component (windowAt base scalar window) part := by
  have quotient : (3*window+part-3)/3+1=window := by omega
  have remainder : (3*window+part-3)%3=part := by omega
  simp only [hintPoint,if_neg (show 3*window+part≠0 by omega),
    if_neg (show 3*window+part≠1 by omega),if_neg (show 3*window+part≠2 by omega),quotient,remainder]

theorem previous (base : curve.Point) (scalar window : Nat) (lower : 1≤window) :
    hintPoint base scalar (3*window-1)=(windowAt base scalar (window-1)).output := by
  by_cases first : window=1
  · subst window
    rfl
  · have quotient : (3*window-1-3)/3+1=window-1 := by omega
    have remainder : (3*window-1-3)%3=2 := by omega
    simp only [hintPoint,if_neg (show 3*window-1≠0 by omega),
      if_neg (show 3*window-1≠1 by omega),if_neg (show 3*window-1≠2 by omega),quotient,remainder,
      AuthorizationTraceSeed451.component,if_neg (show (2:Nat)≠0 by decide),if_neg (show (2:Nat)≠1 by decide)]
end ShielddSecurity.PayloadTraceLocal571
set_option pp.all true in
#check @ShielddSecurity.PayloadTraceLocal571.component
#print axioms ShielddSecurity.PayloadTraceLocal571.component
set_option pp.all true in
#check @ShielddSecurity.PayloadTraceLocal571.previous
#print axioms ShielddSecurity.PayloadTraceLocal571.previous
