import ShielddSecurity.BalanceMapAlgebra693
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.BalanceElligatorAlgebra697

def cubic {F : Type} [CommRing F] (c1 c2 x : F) : F := ((x+c1)*x+c2)*x

theorem alternative {F : Type} [CommRing F] (c1 c2 q x : F)
    (first : (1+q)*x= -c1) : cubic c1 c2 (-x-c1)=q*cubic c1 c2 x := by
  apply sub_eq_zero.mp
  calc
    cubic c1 c2 (-x-c1)-q*cubic c1 c2 x =
      -((1+q)*x+c1)*(x^2+c1*x+c2) := by unfold cubic; ring
    _ = 0 := by simp only [first,neg_add_cancel,neg_zero,zero_mul]

theorem selected_square {F : Type} [CommRing F] (c1 c2 q x y : F) (choice : Bool)
    (first : (1+q)*x= -c1)
    (root : y^2=if choice then cubic c1 c2 x else q*cubic c1 c2 x) :
    y^2=cubic c1 c2 (if choice then x else -x-c1) := by
  cases choice with
  | false =>
    simp only [Bool.false_eq_true,if_false] at root ⊢
    exact root.trans (alternative c1 c2 q x first).symm
  | true =>
    simp only [if_true] at root ⊢
    exact root

theorem scaled {F : Type} [CommRing F] (A K c1 c2 x y : F)
    (linear : c1*K=A) (quadratic : c2*K*K=1) (root : y^2=cubic c1 c2 x) :
    K*(y*K)^2=(x*K)^3+A*(x*K)^2+x*K := by
  calc
    K*(y*K)^2 = K^3*y^2 := by ring
    _ = K^3*cubic c1 c2 x := by rw [root]
    _ = (x*K)^3+(c1*K)*(x*K)^2+(c2*K*K)*(x*K) := by unfold cubic; ring
    _ = (x*K)^3+A*(x*K)^2+x*K := by rw [linear,quadratic,one_mul]

-- Generic algebra only; an actual caller must supply these exact premises.
theorem selected_rational_curve {F : Type} [Field F] [DecidableEq F] (A K d c1 c2 q x y : F) (choice : Bool)
    (coefficient : d*K=A-2) (scale : K=-(A+2)) (nonzero : K≠0)
    (linear : c1*K=A) (quadratic : c2*K*K=1) (first : (1+q)*x= -c1)
    (root : y^2=if choice then cubic c1 c2 x else q*cubic c1 c2 x) :
    let s := (if choice then x else -x-c1)*K;
    let t := y*K;
    let point := if (s+1)*t=0 then ((0:F),(1:F)) else (s/t,(s-1)/(s+1));
    -point.1^2+point.2^2=1+d*point.1^2*point.2^2 := by
  exact BalanceMapAlgebra693.with_identity_branch A K d _ _ coefficient scale nonzero
    (scaled A K c1 c2 _ y linear quadratic (selected_square c1 c2 q x y choice first root))
end ShielddSecurity.BalanceElligatorAlgebra697

set_option pp.all true in
#check @ShielddSecurity.BalanceElligatorAlgebra697.alternative
#print axioms ShielddSecurity.BalanceElligatorAlgebra697.alternative

set_option pp.all true in
#check @ShielddSecurity.BalanceElligatorAlgebra697.selected_square
#print axioms ShielddSecurity.BalanceElligatorAlgebra697.selected_square

set_option pp.all true in
#check @ShielddSecurity.BalanceElligatorAlgebra697.scaled
#print axioms ShielddSecurity.BalanceElligatorAlgebra697.scaled

set_option pp.all true in
#check @ShielddSecurity.BalanceElligatorAlgebra697.selected_rational_curve
#print axioms ShielddSecurity.BalanceElligatorAlgebra697.selected_rational_curve
