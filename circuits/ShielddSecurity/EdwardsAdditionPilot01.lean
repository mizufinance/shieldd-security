import ShielddSecurity.EdwardsWeierstrassEquiv01
import ShielddSecurity.GroupWindows

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.EdwardsAdditionPilot01
open EdwardsWeierstrassEquiv01
variable {F : Type} [Field F] (params : Parameters F)

def addition (left right : Edwards params) : Edwards params :=
  ⟨Group.affineAdd params.d left.val right.val, by
    have den := Group.denominators_nonzero params.d params.imaginary params.nonSquare
      params.imaginarySquare left.val right.val left.property right.property
    exact Group.affine_rows_onCurve params.d params.imaginary params.nonSquare
      params.imaginarySquare left.val right.val _ left.property right.property
      (div_mul_cancel₀ _ den.1) (div_mul_cancel₀ _ den.2)⟩

theorem addition_identity (point : Edwards params) :
    addition params point (identity params) = point := by
  apply Subtype.ext
  cases point with | mk point valid =>
    cases point
    simp [addition, identity, Group.affineAdd, Group.cross, Group.diagonal, Group.delta]

theorem identity_addition (point : Edwards params) :
    addition params (identity params) point = point := by
  apply Subtype.ext
  cases point with | mk point valid =>
    cases point
    simp [addition, identity, Group.affineAdd, Group.cross, Group.diagonal, Group.delta]

theorem addition_comm (left right : Edwards params) :
    addition params left right = addition params right left := by
  apply Subtype.ext
  apply EdwardsWeierstrassEquiv01.point_ext
  · change Group.cross left.val right.val / (1 + Group.delta params.d left.val right.val) =
      Group.cross right.val left.val / (1 + Group.delta params.d right.val left.val)
    congr 1 <;> dsimp only [Group.cross, Group.delta] <;> ring
  · change Group.diagonal left.val right.val / (1 - Group.delta params.d left.val right.val) =
      Group.diagonal right.val left.val / (1 - Group.delta params.d right.val left.val)
    congr 1 <;> dsimp only [Group.diagonal, Group.delta] <;> ring

theorem addition_inverse (point : Edwards params) :
    addition params point (edwardsNeg params point) = identity params := by
  have den := Group.denominators_nonzero params.d params.imaginary params.nonSquare
    params.imaginarySquare point.val (edwardsNeg params point).val point.property
    (edwardsNeg params point).property
  apply Subtype.ext
  apply EdwardsWeierstrassEquiv01.point_ext
  · change (point.val.x * point.val.y + point.val.y * -point.val.x) / _ = 0
    rw [show point.val.x * point.val.y + point.val.y * -point.val.x = 0 by ring]
    exact zero_div _
  · change (point.val.y * point.val.y + point.val.x * -point.val.x) /
      (1 - params.d * point.val.x * -point.val.x * point.val.y * point.val.y) = 1
    apply (div_eq_iff den.2).mpr
    have curve := point.property
    unfold Group.OnCurve at curve
    dsimp only [Group.delta, edwardsNeg]
    linear_combination curve

def torsionTranslate (point : Edwards params) : Edwards params :=
  ⟨⟨-point.val.x, -point.val.y⟩, by simpa [Group.OnCurve] using point.property⟩

theorem torsion_addition (point : Edwards params) :
    addition params (torsion params) point = torsionTranslate params point := by
  apply Subtype.ext
  cases point with | mk point valid =>
    cases point
    simp [addition, torsion, torsionTranslate, Group.affineAdd, Group.cross,
      Group.diagonal, Group.delta]

theorem addition_torsion (point : Edwards params) :
    addition params point (torsion params) = torsionTranslate params point := by
  rw [addition_comm]
  exact torsion_addition params point

end ShielddSecurity.EdwardsAdditionPilot01
