import ShielddSecurity.ConcretePointOperationRows01
import ShielddSecurity.EdwardsTorsionAlgebra01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteOriginAdditionPilot01
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]

/-- Symbolic origin translation, deriving the output equation from Mathlib addition. -/
theorem origin_add_coordinates {X Y : F} (valid : curve.Equation X Y) (nonzeroX : X ≠ 0) :
    ∃ output : curve.Equation (B * B / X) (-B * B * Y / X ^ 2),
      WeierstrassCurve.Affine.Point.mk origin_equation + WeierstrassCurve.Affine.Point.mk valid =
        WeierstrassCurve.Affine.Point.mk output := by
  have slopeRow : (Y / X) * (0 - X) = 0 - Y := by
    field_simp [nonzeroX] <;> ring
  have xRow : B * B / X = (Y / X) ^ 2 - A * B - 0 - X := by
    simpa only [sub_zero] using
      (EdwardsTorsionAlgebra01.origin_secant_x A B X Y nonzeroX
        ((equation_iff _ _).mpr valid)).symm
  have yRow : -B * B * Y / X ^ 2 = (Y / X) * (0 - B * B / X) - 0 := by
    field_simp [nonzeroX] <;> ring
  exact ConcretePointOperationRows01.secant_rows origin_equation valid nonzeroX.symm
    slopeRow xRow yRow

theorem origin_add_origin :
    WeierstrassCurve.Affine.Point.mk origin_equation +
      WeierstrassCurve.Affine.Point.mk origin_equation = 0 :=
  ConcretePointOperationRows01.vertical_addition origin_equation origin_equation rfl (by simp)


set_option pp.all true in
#check @origin_add_coordinates
#print axioms origin_add_coordinates

set_option pp.all true in
#check @origin_add_origin
#print axioms origin_add_origin
end ShielddSecurity.ConcreteOriginAdditionPilot01
