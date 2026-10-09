import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.OrderOfElement

namespace ShielddSecurity.WeierstrassPointImportFloor07
variable {F : Type} [Field F] [DecidableEq F]
theorem actual_add_assoc (curve : WeierstrassCurve.Affine F) (left middle right : curve.Point) :
    (left + middle) + right = left + (middle + right) := add_assoc left middle right
set_option pp.all true in
#check @ShielddSecurity.WeierstrassPointImportFloor07.actual_add_assoc
#print axioms ShielddSecurity.WeierstrassPointImportFloor07.actual_add_assoc
end ShielddSecurity.WeierstrassPointImportFloor07
