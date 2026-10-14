import ShielddSecurity.GroupWindows
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceSignedGroup755
open Group
variable {F : Type} [Field F]

def negate (point : Point F) : Point F := ⟨-point.x,point.y⟩

theorem negate_onCurve (d : F) (point : Point F) (valid : OnCurve d point) :
    OnCurve d (negate point) := by
  simpa only [negate,OnCurve,neg_mul_neg,mul_neg,neg_mul,neg_neg] using valid

theorem add_negate (d imaginary : F) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary=-1) (point : Point F) (valid : OnCurve d point) :
    affineAdd d point (negate point)=identityPoint := by
  have nz := denominators_nonzero d imaginary nonSquare imaginarySquare point (negate point)
    valid (negate_onCurve d point valid)
  have crossZero : cross point (negate point)=0 := by unfold cross negate;ring
  have diag : diagonal point (negate point)=1-delta d point (negate point) := by
    unfold diagonal delta negate
    calc
      point.y*point.y+point.x*(-point.x)=point.y*point.y-point.x*point.x := by ring
      _=1+d*point.x*point.x*point.y*point.y := valid
      _=1-d*point.x*(-point.x)*point.y*point.y := by ring
  simp only [affineAdd,crossZero,diag,zero_div,div_self nz.2,identityPoint]

theorem coordinates_neg {J : Type} [AddCommGroup J] (d imaginary : F)
    (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary=-1) (point : J) :
    model.coordinates (-point)=negate (model.coordinates point) := by
  obtain ⟨inverse,coordinates⟩ := model.covers (negate (model.coordinates point))
    (negate_onCurve d _ (model.onCurve point))
  have zero : point+inverse=0 := model.injective (by
    rw [model.addition,coordinates,add_negate d imaginary nonSquare imaginarySquare _ (model.onCurve point),model.identity])
  have equal : inverse=-point := by
    calc
      inverse=-point+(point+inverse) := by simp only [←add_assoc,neg_add_cancel,zero_add]
      _=-point := by rw [zero,add_zero]
  rw [←equal]
  exact coordinates

theorem reduced_scalar {J : Type} [AddCommGroup J] (point : J) (order : Nat)
    (positive : 0<order) (killed : order • point=0) (scalar : Int) :
    (scalar % (order:Int)).toNat • point=scalar • point := by
  rw [←natCast_zsmul,Int.toNat_of_nonneg (Int.emod_nonneg scalar (by omega))]
  symm
  calc
    scalar • point=(scalar % (order:Int)+(order:Int)*(scalar/(order:Int))) • point := by rw [Int.emod_add_mul_ediv]
    _=(scalar % (order:Int)) • point := by
      rw [add_zsmul,mul_comm (order:Int),mul_zsmul,natCast_zsmul,killed,zsmul_zero,add_zero]
end ShielddSecurity.BalanceSignedGroup755

set_option pp.all true in
#check @ShielddSecurity.BalanceSignedGroup755.negate_onCurve
#print axioms ShielddSecurity.BalanceSignedGroup755.negate_onCurve

set_option pp.all true in
#check @ShielddSecurity.BalanceSignedGroup755.add_negate
#print axioms ShielddSecurity.BalanceSignedGroup755.add_negate

set_option pp.all true in
#check @ShielddSecurity.BalanceSignedGroup755.coordinates_neg
#print axioms ShielddSecurity.BalanceSignedGroup755.coordinates_neg

set_option pp.all true in
#check @ShielddSecurity.BalanceSignedGroup755.reduced_scalar
#print axioms ShielddSecurity.BalanceSignedGroup755.reduced_scalar
