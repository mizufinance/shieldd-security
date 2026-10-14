import ShielddSecurity.CompilerSubgroupArithmetic79
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.MapCofactorArithmetic711
open CompilerSubgroupArithmetic79
variable {F : Type} [Field F]

-- Local arithmetic equations for one captured affine doubling. The numeric
-- offsets match the materialized pivot layout, not source-node numbering.
def Equations (d : F) (point : Group.Point F) (hint : F) (value : Nat → F) : Prop :=
  value 0=point.x*point.x ∧ value 1=point.y*point.y ∧ value 2=value 0*value 1 ∧
  value 4=(1+d*value 2)*(1-d*value 2) ∧ value 6=hint*value 4 ∧
  value 8=point.x*point.y ∧ value 10=point.y*point.x ∧
  value 12=(value 8+value 10)*(1-d*value 2) ∧ value 14=value 12*hint ∧
  value 16=(value 1+value 0)*(1+d*value 2) ∧ value 18=value 16*hint

theorem meaning (d : F) (point : Group.Point F) (hint : F) (value : Nat → F)
    (equations : Equations d point hint value) :
    value 6=hint*inverseProduct d point ∧ Group.Point.mk (value 14) (value 18)=hintStep d point hint := by
  rcases equations with ⟨xx,yy,delta,denom,check,xy,yx,xnum,xout,ynum,yout⟩
  constructor
  · rw [check,denom,delta,xx,yy]
    unfold inverseProduct Group.delta
    ring
  · apply congrArg₂ Group.Point.mk
    · change value 14=Group.cross point point*(1-Group.delta d point point)*hint
      rw [xout,xnum,xy,yx,delta,xx,yy]
      unfold Group.cross Group.delta
      ring
    · change value 18=Group.diagonal point point*(1+Group.delta d point point)*hint
      rw [yout,ynum,delta,xx,yy]
      unfold Group.diagonal Group.delta
      ring

theorem complete (d : F) (point : Group.Point F) (hint : F) (value : Nat → F)
    (equations : Equations d point hint value)
    (chosen : hint=(inverseProduct d point)⁻¹) (nonzero : inverseProduct d point≠0) :
    value 6=1 ∧ Group.Point.mk (value 14) (value 18)=Group.affineAdd d point point := by
  have result := meaning d point hint value equations
  rw [chosen] at result
  refine ⟨result.1.trans (inv_mul_cancel₀ nonzero),?_⟩
  exact result.2.trans (double_affine d point nonzero)
end ShielddSecurity.MapCofactorArithmetic711

set_option pp.all true in
#check @ShielddSecurity.MapCofactorArithmetic711.meaning
#print axioms ShielddSecurity.MapCofactorArithmetic711.meaning

set_option pp.all true in
#check @ShielddSecurity.MapCofactorArithmetic711.complete
#print axioms ShielddSecurity.MapCofactorArithmetic711.complete
