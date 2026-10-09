import ShielddSecurity.EncryptionRegisteredKeyGuard

set_option maxHeartbeats 150000

namespace ShielddSecurity.EncryptionRegisteredKeyCompletion

variable {F : Type} [Field F] [DecidableEq F]

def zeroIndicator (value : F) : F := if value = 0 then 1 else 0

theorem indicator_boolean (value : F) :
    zeroIndicator value = 0 ∨ zeroIndicator value = 1 := by
  by_cases zero : value = 0
  · exact Or.inr (by simp [zeroIndicator, zero])
  · exact Or.inl (by simp [zeroIndicator, zero])

theorem reciprocal (value : F) : value * value⁻¹ = 1 - zeroIndicator value := by
  by_cases zero : value = 0
  · simp [zeroIndicator, zero]
  · simp [zeroIndicator, zero, mul_inv_cancel₀ zero]

theorem annihilator (value : F) : value * zeroIndicator value = 0 := by
  by_cases zero : value = 0 <;> simp [zeroIndicator, zero]

/-- For legal inputs, an unregulated leaf can be the identity; a regulated leaf
must satisfy the independent admission rule. This proves the chosen zero flags
satisfy the forbidden conjunction, without assuming its desired row output. -/
theorem forbidden (point : Group.Point F) (regulated : F)
    (boolean : regulated = 0 ∨ regulated = 1)
    (legal : regulated = 1 → point ≠ Group.identityPoint) :
    regulated * zeroIndicator point.x * zeroIndicator (point.y - 1) = 0 := by
  rcases boolean with inactive | active
  · simp [inactive]
  · by_cases xZero : point.x = 0
    · by_cases yZero : point.y - 1 = 0
      · have identity : point = Group.identityPoint := by
          cases point
          simp_all [Group.identityPoint, sub_eq_zero]
        exact False.elim (legal active identity)
      · simp [zeroIndicator, yZero]
    · simp [zeroIndicator, xZero]

structure Witness (F : Type) where
  zeroX : F
  zeroY : F
  inverseX : F
  inverseY : F
  equal : F
  forbidden : F

def construct (point : Group.Point F) (regulated : F) : Witness F :=
  let zeroX := zeroIndicator point.x
  let zeroY := zeroIndicator (point.y - 1)
  ⟨zeroX, zeroY, point.x⁻¹, (point.y - 1)⁻¹, zeroX * zeroY,
    regulated * (zeroX * zeroY)⟩

structure Equations (point : Group.Point F) (regulated : F) (w : Witness F) : Prop where
  booleanX : w.zeroX = 0 ∨ w.zeroX = 1
  booleanY : w.zeroY = 0 ∨ w.zeroY = 1
  reciprocalX : point.x * w.inverseX = 1 - w.zeroX
  reciprocalY : (point.y - 1) * w.inverseY = 1 - w.zeroY
  annihilatorX : point.x * w.zeroX = 0
  annihilatorY : (point.y - 1) * w.zeroY = 0
  equalProduct : w.equal = w.zeroX * w.zeroY
  forbiddenProduct : w.forbidden = regulated * w.equal
  forbiddenZero : w.forbidden = 0

/-- Algebraic local completeness for both legal branches. Actual finite row
materialization, fresh-column ownership and surrounding-row preservation are
separate obligations; this theorem is not full Transfer completeness. -/
theorem construct_equations (point : Group.Point F) (regulated : F)
    (boolean : regulated = 0 ∨ regulated = 1)
    (legal : regulated = 1 → point ≠ Group.identityPoint) :
    Equations point regulated (construct point regulated) := by
  refine ⟨indicator_boolean point.x, indicator_boolean (point.y - 1),
    reciprocal point.x, reciprocal (point.y - 1), annihilator point.x,
    annihilator (point.y - 1), rfl, rfl, ?_⟩
  change regulated * (zeroIndicator point.x * zeroIndicator (point.y - 1)) = 0
  rw [← mul_assoc]
  exact forbidden point regulated boolean legal

set_option pp.all true in
#check @indicator_boolean
#print axioms indicator_boolean
set_option pp.all true in
#check @reciprocal
#print axioms reciprocal
set_option pp.all true in
#check @annihilator
#print axioms annihilator
set_option pp.all true in
#check @forbidden
#print axioms forbidden
set_option pp.all true in
#check @construct_equations
#print axioms construct_equations

end ShielddSecurity.EncryptionRegisteredKeyCompletion
