import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.MathlibPointImportSmoke01
variable {F : Type} [Field F]

/-- Import/axiom smoke only. This supplies no Edwards addition or native representation join. -/
theorem point_neg_zero (curve : WeierstrassCurve.Affine F) :
    -(0 : curve.Point) = 0 := neg_zero

theorem point_add_assoc (curve : WeierstrassCurve.Affine F) (left middle right : curve.Point) :
    (left + middle) + right = left + (middle + right) := add_assoc left middle right

end ShielddSecurity.MathlibPointImportSmoke01
