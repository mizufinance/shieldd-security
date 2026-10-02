import SpendComparison.Direct
import SpendComparison.Native

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace SpendComparison.Controls
/-- Finite divisor check avoids the global primality decider and extra tactic imports. -/
local instance testPrime : Fact (Nat.Prime 17) := ⟨by
  apply Nat.prime_def_lt.mpr
  refine ⟨by decide, ?_⟩
  have checked : ∀ m : Fin 17, (m : Nat) ∣ 17 → (m : Nat) = 1 := by decide
  intro m below divides
  exact checked ⟨m, below⟩ divides⟩
abbrev TestField := _root_.F 17

/-- Use the primitive ZMod decider, avoiding FiniteField's propext transport. -/
local instance (priority := high) testDecidableEq : DecidableEq TestField :=
  ZMod.decidableEq 17

/-- Computable predicate instances are local to the F17 diagnostics and controls. -/
local instance meaningDecidable (v : Values TestField) : Decidable (Meaning v) := by
  unfold Meaning
  infer_instance

local instance gatesDecidable (v : Values TestField) : Decidable (Gates v) := by
  unfold Gates
  infer_instance

local instance retainedDecidable (omission : Omission) (v : Values TestField) :
    Decidable (RetainedGates omission v) := by
  cases omission <;> unfold RetainedGates <;> infer_instance

def realExample : Values TestField := ⟨0,7,3,3,9,11,11⟩
def dummyExample : Values TestField := ⟨1,0,9,3,9,5,11⟩
def counter : Omission → Values TestField
  | .boolean => ⟨2,0,2,0,1,0,0⟩
  | .selection => ⟨0,0,1,0,0,0,0⟩
  | .root => ⟨0,0,0,0,0,1,0⟩
  | .amount => ⟨1,1,0,0,0,0,0⟩

def constantExpressions (v : Values TestField) : Values (Expression TestField) :=
  ⟨.const v.dummy, .const v.amount, .const v.nullifier, .const v.realNullifier,
    .const v.syntheticNullifier, .const v.computedRoot, .const v.anchor⟩

def testEnvironment : Environment TestField := ⟨fun _ => 0, fun _ _ => #[]⟩

theorem evaluation_preserves (v : Values TestField) :
    Native.evaluated testEnvironment (constantExpressions v) = v := by
  cases v
  rfl

theorem real_positive : Gates realExample ∧ Meaning realExample := by decide
theorem dummy_positive : Gates dummyExample ∧ Meaning dummyExample := by decide

/-- Intended semantic failure: retained equations hold, meaning fails, original rejects. -/
theorem omission_counterexample (omission : Omission) :
    RetainedGates omission (counter omission) ∧
      ¬ Meaning (counter omission) ∧ ¬ Gates (counter omission) := by
  cases omission <;> decide

/-- The same counterassignments satisfy actual weakened Clean operation lists. -/
theorem clean_omission_counterexample (omission : Omission) :
    ConstraintsHold.Soundness testEnvironment
      ((Native.without omission (constantExpressions (counter omission))).operations 0) ∧
    ¬ Meaning (Native.evaluated testEnvironment (constantExpressions (counter omission))) ∧
    ¬ ConstraintsHold.Soundness testEnvironment
      ((Native.main (constantExpressions (counter omission))).operations 0) := by
  simp only [Native.retained_iff, Native.soundness_iff, evaluation_preserves]
  exact omission_counterexample omission

theorem clean_real_positive : ConstraintsHold.Soundness testEnvironment
    ((Native.main (constantExpressions realExample)).operations 0) := by
  rw [Native.soundness_iff, evaluation_preserves]
  exact real_positive.1

theorem clean_dummy_positive : ConstraintsHold.Soundness testEnvironment
    ((Native.main (constantExpressions dummyExample)).operations 0) := by
  rw [Native.soundness_iff, evaluation_preserves]
  exact dummy_positive.1

/-- Executable diagnostics supplement the named kernel proofs; no native_decide. -/
def report (omission : Omission) : Bool :=
  decide (RetainedGates omission (counter omission) ∧
    ¬ Meaning (counter omission) ∧ ¬ Gates (counter omission))

#eval ("PERMANENT_SPEND_F17_POSITIVE_REAL", decide (Gates realExample ∧ Meaning realExample))
#eval ("PERMANENT_SPEND_F17_POSITIVE_DUMMY", decide (Gates dummyExample ∧ Meaning dummyExample))
#eval ("PERMANENT_SPEND_F17_OMIT_BOOLEAN", report .boolean)
#eval ("PERMANENT_SPEND_F17_OMIT_SELECTION", report .selection)
#eval ("PERMANENT_SPEND_F17_OMIT_ROOT", report .root)
#eval ("PERMANENT_SPEND_F17_OMIT_AMOUNT", report .amount)
#eval ("PERMANENT_SPEND_CLEAN_FULL_OPERATIONS",
  ((Native.main (constantExpressions realExample)).operations 0).length)
#eval ("PERMANENT_SPEND_CLEAN_RETAINED_OPERATIONS",
  [Omission.boolean, .selection, .root, .amount].map fun omission =>
    ((Native.without omission (constantExpressions (counter omission))).operations 0).length)

#print axioms evaluation_preserves
#print axioms real_positive
#print axioms dummy_positive
#print axioms omission_counterexample
#print axioms clean_omission_counterexample
#print axioms clean_real_positive
#print axioms clean_dummy_positive
end SpendComparison.Controls
