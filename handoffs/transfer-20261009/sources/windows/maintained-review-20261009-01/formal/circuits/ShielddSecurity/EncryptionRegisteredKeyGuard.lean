import ShielddSecurity.EncryptionDhSelection

set_option maxHeartbeats 150000

namespace ShielddSecurity.EncryptionRegisteredKeyGuard

variable {F : Type} [Field F]

/-- audit.rs's regulated identity exclusion uses the two owned is_zero
reciprocal equations and the forbidden Boolean conjunction. The extracted
source/row certificate must supply those equations on the same assignment.
Neither leaf nonidentity nor its desired multiplication result is assumed. -/
theorem forbidden_identity (point : Group.Point F)
    (regulated zeroX zeroY inverseX inverseY : F)
    (xEquation : point.x * inverseX = 1 - zeroX)
    (yEquation : (point.y - 1) * inverseY = 1 - zeroY)
    (forbidden : regulated * zeroX * zeroY = 0)
    (active : regulated = 1) : point ≠ Group.identityPoint := by
  intro identity
  have xZero : zeroX = 1 := by
    apply Eq.symm
    apply sub_eq_zero.mp
    simpa only [identity, Group.identityPoint, zero_mul] using xEquation.symm
  have yZero : zeroY = 1 := by
    apply Eq.symm
    apply sub_eq_zero.mp
    simpa only [identity, Group.identityPoint, sub_self, zero_mul] using yEquation.symm
  have contradiction : (1 : F) = 0 := by
    simpa only [active, xZero, yZero, one_mul] using forbidden
  exact one_ne_zero contradiction

theorem represented_nonidentity {J : Type} [AddCommGroup J]
    (d : F) (model : Group.StandardCurveModel J d) (point : J)
    (regulated zeroX zeroY inverseX inverseY : F)
    (xEquation : (model.coordinates point).x * inverseX = 1 - zeroX)
    (yEquation : ((model.coordinates point).y - 1) * inverseY = 1 - zeroY)
    (forbidden : regulated * zeroX * zeroY = 0)
    (active : regulated = 1) : point ≠ 0 := by
  have guarded := forbidden_identity (model.coordinates point) regulated zeroX zeroY
    inverseX inverseY xEquation yEquation forbidden active
  intro zero
  rw [zero, model.identity] at guarded
  exact guarded rfl

/-- The registered branch uses its constrained identity exclusion; the
fallback branch uses independently proved fixed initialization nonidentity. -/
theorem selected_nonidentity [DecidableEq F] {J : Type} [AddCommGroup J]
    (d : F) (model : Group.StandardCurveModel J d) (leaf fallback : J)
    (regulated zeroX zeroY inverseX inverseY : F)
    (xEquation : (model.coordinates leaf).x * inverseX = 1 - zeroX)
    (yEquation : ((model.coordinates leaf).y - 1) * inverseY = 1 - zeroY)
    (forbidden : regulated * zeroX * zeroY = 0)
    (fallbackNonzero : fallback ≠ 0) :
    (if regulated = 1 then leaf else fallback) ≠ 0 := by
  by_cases active : regulated = 1
  · rw [if_pos active]
    exact represented_nonidentity d model leaf regulated zeroX zeroY inverseX inverseY
      xEquation yEquation forbidden active
  · rw [if_neg active]
    exact fallbackNonzero

theorem selected_coordinates_nonidentity [DecidableEq F]
    {J : Type} [AddCommGroup J]
    (d : F) (model : Group.StandardCurveModel J d) (leaf fallback : J)
    (regulated zeroX zeroY inverseX inverseY : F)
    (boolean : regulated = 0 ∨ regulated = 1)
    (xEquation : (model.coordinates leaf).x * inverseX = 1 - zeroX)
    (yEquation : ((model.coordinates leaf).y - 1) * inverseY = 1 - zeroY)
    (forbidden : regulated * zeroX * zeroY = 0)
    (fallbackNonzero : fallback ≠ 0) :
    EncryptionDhSelection.select regulated (model.coordinates leaf)
      (model.coordinates fallback) ≠ Group.identityPoint := by
  rw [EncryptionDhSelection.represented_selection model regulated leaf fallback boolean,
    ← model.identity]
  intro zero
  exact selected_nonidentity d model leaf fallback regulated zeroX zeroY inverseX inverseY
    xEquation yEquation forbidden fallbackNonzero (model.injective zero)

set_option pp.all true in
#check @forbidden_identity
#print axioms forbidden_identity
set_option pp.all true in
#check @represented_nonidentity
#print axioms represented_nonidentity
set_option pp.all true in
#check @selected_nonidentity
#print axioms selected_nonidentity
set_option pp.all true in
#check @selected_coordinates_nonidentity
#print axioms selected_coordinates_nonidentity

end ShielddSecurity.EncryptionRegisteredKeyGuard
