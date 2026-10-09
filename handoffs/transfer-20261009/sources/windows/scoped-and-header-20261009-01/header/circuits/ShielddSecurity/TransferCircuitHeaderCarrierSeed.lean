import ShielddSecurity.TransferCircuitHeaderInputs

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferCircuitHeaderCarrierSeed
open TransferSem

/-! Join source witness input indices to the compiler seed for one public and
one committed input. The ordinary private input columns begin at three.
The final claimed-statement input is computed from the constructed semantic
witness. All remaining gadget inputs are supplied, not proved legal here.
The local row bodies below need exact indexed inclusion in the complete pinned
relation before they can support a full relation claim. -/

def privateColumn (input : Fin 22735) : Nat := 3 + input.val

def sourceInputs {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (remainingInputs : Nat → F) : Nat → F :=
  fun input => if input = 22734 then (TransferCircuitInputSeed.statementValue c i : F)
    else TransferCircuitHeaderInputs.values
      (TransferSemanticConstruction.construct c i) remainingInputs input

def rawColumns {F : Type} [Field F] (inputs remainingColumns : Nat → F) : Nat → F :=
  fun column => if 3 ≤ column ∧ column < 22738 then inputs (column - 3)
    else remainingColumns column

def assignment {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (remainingInputs remainingColumns : Nat → F) : Nat → F :=
  TransferCircuitInputSeed.seed c i
    (rawColumns (sourceInputs c i remainingInputs) remainingColumns)

theorem private_inputs_preserved {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (remainingInputs remainingColumns : Nat → F)
    (input : Fin 22735) :
    assignment c i remainingInputs remainingColumns (privateColumn input) =
      sourceInputs c i remainingInputs input.val := by
  have outside : privateColumn input ∉ TransferCircuitInputSeed.keptColumns := by
    simp only [privateColumn, TransferCircuitInputSeed.keptColumns,
      TransferCircuitInputSeed.constantCopy, List.mem_cons, List.not_mem_nil, or_false, not_or]
    have bounded := input.isLt
    omega
  have bounds : 3 ≤ privateColumn input ∧ privateColumn input < 22738 := by
    have bounded := input.isLt
    simp only [privateColumn]
    omega
  have offset : privateColumn input - 3 = input.val := by simp [privateColumn]
  unfold assignment
  rw [TransferCircuitInputSeed.seed_other_columns c i _ _ outside]
  simp only [rawColumns, if_pos bounds, offset]

theorem blinding_private_input {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (remainingInputs remainingColumns : Nat → F) :
    assignment c i remainingInputs remainingColumns 9 =
      ((TransferSemanticConstruction.construct c i).blinding : F) := by
  simpa [privateColumn, sourceInputs, TransferCircuitHeaderInputs.values] using
    private_inputs_preserved c i remainingInputs remainingColumns ⟨6, by decide⟩

theorem committed_private_blinding_link {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (remainingInputs remainingColumns : Nat → F) :
    assignment c i remainingInputs remainingColumns 2 =
      assignment c i remainingInputs remainingColumns 9 := by
  exact (TransferCircuitInputSeed.seed_roles c i _).2.2.1.trans
    (blinding_private_input c i remainingInputs remainingColumns).symm

theorem claimed_statement_private_input {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (remainingInputs remainingColumns : Nat → F) :
    assignment c i remainingInputs remainingColumns 22737 =
      (TransferCircuitInputSeed.statementValue c i : F) := by
  simpa [privateColumn, sourceInputs] using
    private_inputs_preserved c i remainingInputs remainingColumns ⟨22734, by decide⟩

theorem public_private_statement_link {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (remainingInputs remainingColumns : Nat → F) :
    assignment c i remainingInputs remainingColumns 1 =
      assignment c i remainingInputs remainingColumns 22737 := by
  exact (TransferCircuitInputSeed.seed_roles c i _).2.1.trans
    (claimed_statement_private_input c i remainingInputs remainingColumns).symm

def headerRows : List Row :=
  [booleanRow 10, ⟨[(1, 1), (22737, -1)], []⟩, ⟨[(2, 1), (9, -1)], []⟩,
    ⟨[(0, 1), (TransferCircuitInputSeed.constantCopy, -1)], []⟩]

theorem header_rows_complete {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (remainingInputs remainingColumns : Nat → F) :
    Satisfies (assignment c i remainingInputs remainingColumns) headerRows := by
  have roles := TransferCircuitInputSeed.seed_roles c i
    (rawColumns (sourceInputs c i remainingInputs) remainingColumns)
  change assignment c i remainingInputs remainingColumns 0 = 1 ∧
    assignment c i remainingInputs remainingColumns 1 = (TransferCircuitInputSeed.statementValue c i : F) ∧
    assignment c i remainingInputs remainingColumns 2 = ((TransferSemanticConstruction.construct c i).blinding : F) ∧
    assignment c i remainingInputs remainingColumns TransferCircuitInputSeed.constantCopy = 1 at roles
  have regulated : assignment c i remainingInputs remainingColumns 10 =
      TransferCircuitHeaderInputs.values (TransferSemanticConstruction.construct c i) remainingInputs 7 := by
    simpa [privateColumn, sourceInputs] using
      private_inputs_preserved c i remainingInputs remainingColumns ⟨7, by decide⟩
  have link := committed_private_blinding_link c i remainingInputs remainingColumns
  have publicLink := public_private_statement_link c i remainingInputs remainingColumns
  intro row present
  simp only [headerRows, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · simpa only [booleanRow, eval, Int.cast_one, one_mul, add_zero, regulated] using
      TransferCircuitHeaderInputs.constructed_regulated_assertion c i remainingInputs
  · simp [Square, eval, publicLink]
  · simp [Square, eval, link]
  · simp [Square, eval, roles.1, roles.2.2.2]

set_option pp.all true in
#check @private_inputs_preserved
#print axioms private_inputs_preserved
set_option pp.all true in
#check @blinding_private_input
#print axioms blinding_private_input
set_option pp.all true in
#check @committed_private_blinding_link
#print axioms committed_private_blinding_link
set_option pp.all true in
#check @claimed_statement_private_input
#print axioms claimed_statement_private_input
set_option pp.all true in
#check @public_private_statement_link
#print axioms public_private_statement_link
set_option pp.all true in
#check @header_rows_complete
#print axioms header_rows_complete

end ShielddSecurity.TransferCircuitHeaderCarrierSeed
