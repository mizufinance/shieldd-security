import ShielddSecurity.TransferSemanticInputRecovery
import ShielddSecurity.CompilerCompletion

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferCircuitInputSeed
open TransferSem

/-! Construct the reserved compiler input columns from ordered raw semantic
inputs. Other witness columns remain supplied by the owned raw algorithm.
Structural compiler preservation needs no assertion truth or row satisfaction.
This seed is not a completed circuit assignment. Binding these role numbers to
the complete pinned compiler instance remains a concrete data obligation. -/

def constantCopy : Nat := 200692

def keptColumns : List Nat := [0, 1, 2, constantCopy]

def statementValue (c : Crypto) (i : TransferSemanticConstruction.Inputs c) : Nat :=
  c.hash .transferStatement (publicFields c (TransferSemanticConstruction.construct c i))

def seed {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (witnessColumns : Nat → F) : Nat → F :=
  fun column =>
    if column = 0 then 1 else
    if column = 1 then (statementValue c i : F) else
    if column = 2 then ((TransferSemanticConstruction.construct c i).blinding : F) else
    if column = constantCopy then 1 else witnessColumns column

theorem seed_roles {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (witnessColumns : Nat → F) :
    seed c i witnessColumns 0 = 1 ∧
      seed c i witnessColumns 1 = (statementValue c i : F) ∧
      seed c i witnessColumns 2 = ((TransferSemanticConstruction.construct c i).blinding : F) ∧
      seed c i witnessColumns constantCopy = 1 := by
  simp [seed, constantCopy]

theorem seed_other_columns {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (witnessColumns : Nat → F)
    (column : Nat) (outside : column ∉ keptColumns) :
    seed c i witnessColumns column = witnessColumns column := by
  simp only [keptColumns, List.mem_cons, not_or] at outside
  simp only [seed, if_neg outside.1, if_neg outside.2.1,
    if_neg outside.2.2.1, if_neg outside.2.2.2.1]

theorem run_roles_preserved {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (witnessColumns : Nat → F)
    (steps : List CompilerCompletion.Step)
    (ordered : CompilerCompletion.Topological keptColumns [] steps) :
    CompilerCompletion.run (seed c i witnessColumns) steps 0 = 1 ∧
      CompilerCompletion.run (seed c i witnessColumns) steps 1 = (statementValue c i : F) ∧
      CompilerCompletion.run (seed c i witnessColumns) steps 2 =
        ((TransferSemanticConstruction.construct c i).blinding : F) ∧
      CompilerCompletion.run (seed c i witnessColumns) steps constantCopy = 1 := by
  have preserves := CompilerCompletion.run_preserves
    (seed c i witnessColumns) steps keptColumns [] ordered
  have roles := seed_roles c i witnessColumns
  exact ⟨(preserves 0 (by simp [keptColumns])).trans roles.1,
    (preserves 1 (by simp [keptColumns])).trans roles.2.1,
    (preserves 2 (by simp [keptColumns])).trans roles.2.2.1,
    (preserves constantCopy (by simp [keptColumns])).trans roles.2.2.2⟩

theorem recovered_seed_roles {F : Type} [Field F] (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c)
    (legal : TransferSem.TransferSem c w) (witnessColumns : Nat → F) :
    seed c (TransferSemanticInputRecovery.recover c w zeroMul legal) witnessColumns 0 = 1 ∧
      seed c (TransferSemanticInputRecovery.recover c w zeroMul legal) witnessColumns 1 =
        (c.hash .transferStatement (publicFields c w) : F) ∧
      seed c (TransferSemanticInputRecovery.recover c w zeroMul legal) witnessColumns 2 =
        (w.blinding : F) ∧
      seed c (TransferSemanticInputRecovery.recover c w zeroMul legal) witnessColumns constantCopy = 1 := by
  have roles := seed_roles c (TransferSemanticInputRecovery.recover c w zeroMul legal) witnessColumns
  have inputs := TransferSemanticInputRecovery.relation_inputs_preserved c w zeroMul legal
  unfold statementValue at roles
  rw [inputs.1, inputs.2] at roles
  exact roles

theorem recovered_run_roles {F : Type} [Field F] (c : Crypto) (w : TransferSem.Witness)
    (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c)
    (legal : TransferSem.TransferSem c w) (witnessColumns : Nat → F)
    (steps : List CompilerCompletion.Step)
    (ordered : CompilerCompletion.Topological keptColumns [] steps) :
    CompilerCompletion.run
        (seed c (TransferSemanticInputRecovery.recover c w zeroMul legal) witnessColumns) steps 0 = 1 ∧
      CompilerCompletion.run
        (seed c (TransferSemanticInputRecovery.recover c w zeroMul legal) witnessColumns) steps 1 =
        (c.hash .transferStatement (publicFields c w) : F) ∧
      CompilerCompletion.run
        (seed c (TransferSemanticInputRecovery.recover c w zeroMul legal) witnessColumns) steps 2 =
        (w.blinding : F) ∧
      CompilerCompletion.run
        (seed c (TransferSemanticInputRecovery.recover c w zeroMul legal) witnessColumns) steps constantCopy = 1 := by
  have roles := run_roles_preserved c
    (TransferSemanticInputRecovery.recover c w zeroMul legal) witnessColumns steps ordered
  have inputs := TransferSemanticInputRecovery.relation_inputs_preserved c w zeroMul legal
  unfold statementValue at roles
  rw [inputs.1, inputs.2] at roles
  exact roles

set_option pp.all true in
#check @seed_roles
#print axioms seed_roles
set_option pp.all true in
#check @seed_other_columns
#print axioms seed_other_columns
set_option pp.all true in
#check @run_roles_preserved
#print axioms run_roles_preserved
set_option pp.all true in
#check @recovered_seed_roles
#print axioms recovered_seed_roles
set_option pp.all true in
#check @recovered_run_roles
#print axioms recovered_run_roles

end ShielddSecurity.TransferCircuitInputSeed
