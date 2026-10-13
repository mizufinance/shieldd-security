import ShielddSecurity.VariableAddTemplate433
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableOperationAdapter434
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariablePortSubstitution432

structure Entry where
  isAdd : Bool
  ports : List Linear
  arithmeticStart : Nat
  arithmeticRows : List Row
  assertionStart : Nat
  assertionRows : List Row

def port (entry : Entry) (index : Nat) : Linear := entry.ports.getD index []
def templateArithmetic (entry : Entry) : List Row :=
  rows (port entry) (if entry.isAdd then VariableAddTemplate433.arithmeticRows else VariableDoubleTemplate431.arithmeticRows)
def templateAssertions (entry : Entry) : List Row :=
  rows (port entry) (if entry.isAdd then VariableAddTemplate433.assertionRows else VariableDoubleTemplate431.assertionRows)
def covers (expected actual : List Row) : Bool :=
  CompilerIndexed01.checkOriginalCoverage p 0 expected.toArray actual.toArray (List.range expected.length).toArray

def Valid (entry : Entry) : Prop :=
  CompilerRowSlice63.check CapturedFullArithmetic52.rowAt entry.arithmeticStart entry.arithmeticRows.length entry.arithmeticRows=true ∧
  entry.arithmeticStart+entry.arithmeticRows.length≤177954 ∧
  CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+entry.assertionStart) 2 entry.assertionRows=true ∧
  entry.assertionStart+2≤22816 ∧
  covers (templateArithmetic entry) entry.arithmeticRows=true ∧
  covers (templateAssertions entry) entry.assertionRows=true ∧
  covers entry.assertionRows (templateAssertions entry)=true ∧
  port entry 0=[(copy,1)]
noncomputable instance validDecidable (entry : Entry) : Decidable (Valid entry) := by
  unfold Valid
  infer_instance
noncomputable def check (entry : Entry) : Bool := decide (Valid entry)

def Equations {F : Type} [Field F] (rho : Nat → F) (entry : Entry) : Prop :=
  let v := fun i => eval rho (port entry i)
  if entry.isAdd then
    TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:F) ⟨v 1,v 2⟩ ⟨v 3,v 4⟩ ⟨v 5,v 6⟩
  else TransferOwnership.DoubleEquations ⟨v 1,v 2⟩ ⟨v 3,v 4⟩

def Rows {F : Type} [Field F] (rho : Nat → F) (entry : Entry) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+entry.assertionStart+i)) 2

variable {F : Type} [Field F] [CharP F p]
theorem equations_iff (entry : Entry) (checked : check entry=true) (rho : Nat → F)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    Rows rho entry ↔ Equations rho entry := by
  have valid : Valid entry := of_decide_eq_true checked
  rcases valid with ⟨actual,inside,assertions,assertionBound,arithmeticShape,forward,reverse,constant⟩
  have localArithmetic := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954
    entry.arithmeticStart entry.arithmeticRows.length entry.arithmeticRows actual inside rho arithmetic
  have templateArithmeticSat := transfer rho (templateArithmetic entry) entry.arithmeticRows arithmeticShape localArithmetic
  have templateOne : eval rho (port entry 0)=1 := by rw [constant];simp only [eval,Int.cast_one,one_mul,add_zero,one]
  have shapes : Satisfies rho entry.assertionRows ↔ Satisfies rho (templateAssertions entry) :=
    ⟨transfer rho _ _ forward,transfer rho _ _ reverse⟩
  change SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+entry.assertionStart+i)) 2 ↔ _
  rw [←CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+entry.assertionStart) 2 entry.assertionRows assertions rho,shapes]
  cases kind : entry.isAdd with
  | false =>
    simp only [templateAssertions,templateArithmetic,Equations,kind,Bool.false_eq_true,if_false] at templateArithmeticSat ⊢
    exact VariablePortSubstitution432.double_iff (port entry) rho templateOne templateArithmeticSat
  | true =>
    simp only [templateAssertions,templateArithmetic,Equations,kind,if_true] at templateArithmeticSat ⊢
    rw [satisfies_rows]
    exact VariableAddTemplate433.add_iff _ templateOne ((satisfies_rows _ _ _).mp templateArithmeticSat)
end ShielddSecurity.VariableOperationAdapter434

set_option pp.all true in
#check @ShielddSecurity.VariableOperationAdapter434.Entry
#print axioms ShielddSecurity.VariableOperationAdapter434.Entry

set_option pp.all true in
#check @ShielddSecurity.VariableOperationAdapter434.port
#print axioms ShielddSecurity.VariableOperationAdapter434.port

set_option pp.all true in
#check @ShielddSecurity.VariableOperationAdapter434.templateArithmetic
#print axioms ShielddSecurity.VariableOperationAdapter434.templateArithmetic

set_option pp.all true in
#check @ShielddSecurity.VariableOperationAdapter434.templateAssertions
#print axioms ShielddSecurity.VariableOperationAdapter434.templateAssertions

set_option pp.all true in
#check @ShielddSecurity.VariableOperationAdapter434.covers
#print axioms ShielddSecurity.VariableOperationAdapter434.covers

set_option pp.all true in
#check @ShielddSecurity.VariableOperationAdapter434.Valid
#print axioms ShielddSecurity.VariableOperationAdapter434.Valid

set_option pp.all true in
#check @ShielddSecurity.VariableOperationAdapter434.check
#print axioms ShielddSecurity.VariableOperationAdapter434.check

set_option pp.all true in
#check @ShielddSecurity.VariableOperationAdapter434.Equations
#print axioms ShielddSecurity.VariableOperationAdapter434.Equations

set_option pp.all true in
#check @ShielddSecurity.VariableOperationAdapter434.Rows
#print axioms ShielddSecurity.VariableOperationAdapter434.Rows

set_option pp.all true in
#check @ShielddSecurity.VariableOperationAdapter434.equations_iff
#print axioms ShielddSecurity.VariableOperationAdapter434.equations_iff

set_option pp.all true in
#check @ShielddSecurity.VariableOperationAdapter434.validDecidable
#print axioms ShielddSecurity.VariableOperationAdapter434.validDecidable
