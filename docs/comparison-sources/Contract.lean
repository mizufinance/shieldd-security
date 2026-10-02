import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring.RingNF

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace SpendComparison

/-- The seven semantic inputs are preserved; this spike allocates no auxiliary. -/
structure Values (F : Type) where
  dummy : F
  amount : F
  nullifier : F
  realNullifier : F
  syntheticNullifier : F
  computedRoot : F
  anchor : F

variable {F : Type} [Field F]

/-- Independent permanent-spend meaning, with no hash/history/range premise. -/
def Meaning (v : Values F) : Prop :=
  (v.dummy = 0 ∧ v.nullifier = v.realNullifier ∧ v.computedRoot = v.anchor) ∨
  (v.dummy = 1 ∧ v.amount = 0 ∧ v.nullifier = v.syntheticNullifier)

def Gates (v : Values F) : Prop :=
  v.dummy * v.dummy = v.dummy ∧
  v.nullifier = v.dummy * v.syntheticNullifier + (1-v.dummy) * v.realNullifier ∧
  (1-v.dummy) * (v.computedRoot-v.anchor) = 0 ∧ v.dummy * v.amount = 0

/-- Shared algebraic reasoning; the two arms do not claim independent proofs. -/
theorem gates_sound (v : Values F) (holds : Gates v) : Meaning v := by
  rcases holds with ⟨boolean, selected, root, amount⟩
  have split : v.dummy * (v.dummy-1) = 0 := by
    calc
      _ = v.dummy * v.dummy - v.dummy := by ring
      _ = 0 := by rw [boolean, sub_self]
  rcases mul_eq_zero.mp split with zero | one
  · left
    exact ⟨zero, by simpa [zero] using selected,
      sub_eq_zero.mp (by simpa [zero] using root)⟩
  · have one' : v.dummy = 1 := sub_eq_zero.mp one
    right
    exact ⟨one', by simpa [one'] using amount, by simpa [one'] using selected⟩

theorem gates_complete (v : Values F) (legal : Meaning v) : Gates v := by
  rcases legal with ⟨zero, real, root⟩ | ⟨one, amount, synthetic⟩
  · simp [Gates, zero, real, root]
  · simp [Gates, one, amount, synthetic]

inductive Omission where
  | boolean | selection | root | amount
  deriving DecidableEq, Repr

/-- A control removes exactly one equation, keeping the other three. -/
def RetainedGates (omission : Omission) (v : Values F) : Prop :=
  match omission with
  | .boolean =>
    v.nullifier = v.dummy*v.syntheticNullifier + (1-v.dummy)*v.realNullifier ∧
    (1-v.dummy)*(v.computedRoot-v.anchor) = 0 ∧ v.dummy*v.amount = 0
  | .selection =>
    v.dummy*v.dummy = v.dummy ∧
    (1-v.dummy)*(v.computedRoot-v.anchor) = 0 ∧ v.dummy*v.amount = 0
  | .root =>
    v.dummy*v.dummy = v.dummy ∧
    v.nullifier = v.dummy*v.syntheticNullifier + (1-v.dummy)*v.realNullifier ∧
    v.dummy*v.amount = 0
  | .amount =>
    v.dummy*v.dummy = v.dummy ∧
    v.nullifier = v.dummy*v.syntheticNullifier + (1-v.dummy)*v.realNullifier ∧
    (1-v.dummy)*(v.computedRoot-v.anchor) = 0

#print axioms gates_sound
#print axioms gates_complete
end SpendComparison
