import ShielddSecurity.CompilerSubgroupArithmetic79
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerSubgroupClosure83
open CompilerSubgroupArithmetic79
variable {F : Type} [Field F]
theorem inverse_nonzero (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (point : Group.Point F)
    (valid : Group.OnCurve d point) : inverseProduct d point≠0 := by
  have result:=Group.denominators_nonzero d imaginary nonSquare imaginarySquare point point valid valid
  exact mul_ne_zero result.1 result.2
-- A cleared polynomial identity; the inverse is never reduced numerically.
theorem double_curve (d : F) (point : Group.Point F) (valid : Group.OnCurve d point)
    (nonzero : inverseProduct d point≠0) : Group.OnCurve d (double d point) := by
  let x:=point.x
  let y:=point.y
  let plus:=1+d*x*x*y*y
  let minus:=1-d*x*x*y*y
  let q:=plus*minus
  let xn:=(x*y+y*x)*minus
  let yn:=(y*y+x*x)*plus
  have hq : q≠0 := nonzero
  have inv : q*q⁻¹=1 := mul_inv_cancel₀ hq
  have polynomial : q^2*(yn^2-xn^2)-q^4-d*xn^2*yn^2 =
      q^2*minus^2*(y*y-x*x-plus)*(y*y-x*x+plus) := by
    dsimp only [q,plus,minus,xn,yn]
    ring
  have relation : y*y-x*x=plus := valid
  have zero : q^2*(yn^2-xn^2)-q^4-d*xn^2*yn^2=0 := by
    rw [polynomial,relation,sub_self,mul_zero,zero_mul]
  have cleared : q^4*((yn*q⁻¹)^2-(xn*q⁻¹)^2-1-d*(xn*q⁻¹)^2*(yn*q⁻¹)^2)=0 := by
    calc
      _ = (q*q⁻¹)^2*q^2*(yn^2-xn^2)-q^4-d*(q*q⁻¹)^4*xn^2*yn^2 := by ring
      _ = _ := by rw [inv]; simpa only [one_pow,one_mul,mul_one] using zero
  have difference : (yn*q⁻¹)^2-(xn*q⁻¹)^2-1-d*(xn*q⁻¹)^2*(yn*q⁻¹)^2=0 :=
    (mul_eq_zero.mp cleared).resolve_left (pow_ne_zero 4 hq)
  change (yn*q⁻¹)*(yn*q⁻¹)-(xn*q⁻¹)*(xn*q⁻¹)=
    1+d*(xn*q⁻¹)*(xn*q⁻¹)*(yn*q⁻¹)*(yn*q⁻¹)
  have rearranged := sub_eq_zero.mp difference
  calc
    _ = ((yn*q⁻¹)^2-(xn*q⁻¹)^2) := by ring
    _ = 1+d*(xn*q⁻¹)^2*(yn*q⁻¹)^2 := by
      have equality := (sub_eq_iff_eq_add).mp rearranged
      simpa only [add_comm] using equality
    _ = _ := by ring
theorem trace_curve (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (point : Group.Point F)
    (valid : Group.OnCurve d point) (count : Nat) : Group.OnCurve d (trace d point count) := by
  induction count with
  | zero => exact valid
  | succ count ih =>
    exact double_curve d (trace d point count) ih
      (inverse_nonzero d imaginary nonSquare imaginarySquare _ ih)
theorem trace_denominators (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (point : Group.Point F)
    (valid : Group.OnCurve d point) (count : Nat) : inverseProduct d (trace d point count)≠0 :=
  inverse_nonzero d imaginary nonSquare imaginarySquare _
    (trace_curve d imaginary nonSquare imaginarySquare point valid count)
end ShielddSecurity.CompilerSubgroupClosure83
