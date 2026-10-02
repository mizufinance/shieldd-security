import SpendComparison.Contract
import Clean.Circuit.Basic

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace SpendComparison.Native
variable {F : Type} [FiniteField F]

def evaluated (env : Environment F) (v : Values (Expression F)) : Values F :=
  ⟨env v.dummy, env v.amount, env v.nullifier, env v.realNullifier,
    env v.syntheticNullifier, env v.computedRoot, env v.anchor⟩

def boolean (v : Values (Expression F)) : Expression F := v.dummy*v.dummy-v.dummy
def selection (v : Values (Expression F)) : Expression F :=
  v.nullifier-(v.dummy*v.syntheticNullifier+(1-v.dummy)*v.realNullifier)
def root (v : Values (Expression F)) : Expression F := (1-v.dummy)*(v.computedRoot-v.anchor)
def amount (v : Values (Expression F)) : Expression F := v.dummy*v.amount

/-- Actual Clean Circuit assertions, not an alias of the direct gate predicate. -/
def main (v : Values (Expression F)) : Circuit F Unit := do
  Circuit.assertZero (boolean v)
  Circuit.assertZero (selection v)
  Circuit.assertZero (root v)
  Circuit.assertZero (amount v)

theorem operations_exact (v : Values (Expression F)) (offset : Nat) :
    (main v).operations offset =
      [.assert (boolean v), .assert (selection v), .assert (root v), .assert (amount v)] := rfl

theorem soundness_iff (env : Environment F) (v : Values (Expression F)) (offset : Nat) :
    ConstraintsHold.Soundness env ((main v).operations offset) ↔ Gates (evaluated env v) := by
  rw [operations_exact]
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset, Gates, evaluated,
    boolean, selection, root, amount, _root_.eval_sub, _root_.eval_mul,
    _root_.eval_add, Expression.eval, neg_one_mul, Expression.add_neg_eq_sub,
    sub_eq_zero, and_true]

theorem completeness_iff (env : ProverEnvironment F) (v : Values (Expression F)) (offset : Nat) :
    ConstraintsHold.Completeness env ((main v).operations offset) ↔
      Gates (evaluated env.toEnvironment v) := by
  rw [operations_exact]
  simp only [ConstraintsHold.Completeness, Operations.forAllNoOffset, Gates, evaluated,
    boolean, selection, root, amount, _root_.eval_sub, _root_.eval_mul,
    _root_.eval_add, Expression.eval, neg_one_mul, Expression.add_neg_eq_sub,
    sub_eq_zero, and_true]

theorem sound (env : Environment F) (v : Values (Expression F)) (offset : Nat)
    (holds : ConstraintsHold.Soundness env ((main v).operations offset)) :
    Meaning (evaluated env v) := gates_sound _ ((soundness_iff env v offset).mp holds)

/-- Every legal seven-field input satisfies actual Clean assertions unchanged. -/
theorem complete (env : ProverEnvironment F) (v : Values (Expression F)) (offset : Nat)
    (legal : Meaning (evaluated env.toEnvironment v)) :
    ConstraintsHold.Completeness env ((main v).operations offset) :=
  (completeness_iff env v offset).mpr (gates_complete _ legal)

theorem no_new_wires (v : Values (Expression F)) (offset : Nat) :
    Circuit.localLength (main v) offset = 0 := rfl

/-- Preservation is literal identity; no WitgenIR witness operation is emitted. -/
def completeInput (v : Values (Expression F)) : Values (Expression F) := v

theorem completion_preserves (v : Values (Expression F)) : completeInput v = v := rfl

def without (omission : Omission) (v : Values (Expression F)) : Circuit F Unit :=
  match omission with
  | .boolean => do
    Circuit.assertZero (selection v)
    Circuit.assertZero (root v)
    Circuit.assertZero (amount v)
  | .selection => do
    Circuit.assertZero (boolean v)
    Circuit.assertZero (root v)
    Circuit.assertZero (amount v)
  | .root => do
    Circuit.assertZero (boolean v)
    Circuit.assertZero (selection v)
    Circuit.assertZero (amount v)
  | .amount => do
    Circuit.assertZero (boolean v)
    Circuit.assertZero (selection v)
    Circuit.assertZero (root v)

theorem retained_iff (omission : Omission) (env : Environment F)
    (v : Values (Expression F)) (offset : Nat) :
    ConstraintsHold.Soundness env ((without omission v).operations offset) ↔
      RetainedGates omission (evaluated env v) := by
  cases omission <;>
    simp only [without, RetainedGates, Circuit.operations, circuit_norm, evaluated,
      boolean, selection, root, amount, _root_.eval_sub, _root_.eval_mul,
      _root_.eval_add, Expression.eval, neg_one_mul, Expression.add_neg_eq_sub,
      sub_eq_zero, and_true]

#print axioms operations_exact
#print axioms soundness_iff
#print axioms completeness_iff
#print axioms sound
#print axioms complete
#print axioms no_new_wires
#print axioms completion_preserves
#print axioms retained_iff
end SpendComparison.Native
