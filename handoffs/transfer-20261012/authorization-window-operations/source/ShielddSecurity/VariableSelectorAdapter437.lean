import ShielddSecurity.VariableSelectorTemplate436
import ShielddSecurity.VariableOperationAdapter434
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableSelectorAdapter437
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariablePortSubstitution432
structure Entry where
  ports : List Linear
  arithmeticStart : Nat
  arithmeticRows : List Row
  outputX : Linear
  outputY : Linear
def port (entry : Entry) (index : Nat) : Linear := entry.ports.getD index []
def templateArithmetic (entry : Entry) : List Row := rows (port entry) VariableSelectorTemplate436.arithmeticRows
def expectedX (entry : Entry) : Linear := linear (port entry) [(11,1),(13,1)]
def expectedY (entry : Entry) : Linear := linear (port entry) [(0,1),(17,1),(19,1)]
def Valid (entry : Entry) : Prop :=
  CompilerRowSlice63.check CapturedFullArithmetic52.rowAt entry.arithmeticStart entry.arithmeticRows.length entry.arithmeticRows=true ∧
  entry.arithmeticStart+entry.arithmeticRows.length≤177954 ∧
  VariableOperationAdapter434.covers (templateArithmetic entry) entry.arithmeticRows=true ∧
  canonical p entry.outputX=canonical p (expectedX entry) ∧
  canonical p entry.outputY=canonical p (expectedY entry) ∧
  port entry 0=[(copy,1)]
noncomputable instance validDecidable (entry : Entry) : Decidable (Valid entry) := by
  unfold Valid
  infer_instance
noncomputable def check (entry : Entry) : Bool := decide (Valid entry)
variable {F : Type} [Field F] [CharP F p]
theorem coordinates (entry : Entry) (checked : check entry=true) (rho : Nat → F)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    Group.Point.mk (eval rho entry.outputX) (eval rho entry.outputY) =
    Group.windowPoint (eval rho (port entry 1)) (eval rho (port entry 2))
      ⟨eval rho (port entry 3),eval rho (port entry 4)⟩
      ⟨eval rho (port entry 5),eval rho (port entry 6)⟩
      ⟨eval rho (port entry 7),eval rho (port entry 8)⟩ := by
  have valid : Valid entry := of_decide_eq_true checked
  rcases valid with ⟨actual,inside,shape,x,y,constant⟩
  have localArithmetic := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954
    entry.arithmeticStart entry.arithmeticRows.length entry.arithmeticRows actual inside rho arithmetic
  have templ := transfer rho (templateArithmetic entry) entry.arithmeticRows shape localArithmetic
  have templateOne : eval rho (port entry 0)=1 := by
    rw [constant];simp only [eval,Int.cast_one,one_mul,add_zero,one]
  have result := VariableSelectorTemplate436.coordinates (fun i => eval rho (port entry i)) templateOne
    ((satisfies_rows _ _ _).mp templ)
  have hx := canonical_equal rho entry.outputX (expectedX entry) x
  have hy := canonical_equal rho entry.outputY (expectedY entry) y
  rw [hx,hy]
  simpa only [expectedX,expectedY,eval_linear,eval,Int.cast_one,one_mul,add_zero,
    VariableSelectorTemplate436.output,add_assoc] using result
end ShielddSecurity.VariableSelectorAdapter437

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorAdapter437.Entry
#print axioms ShielddSecurity.VariableSelectorAdapter437.Entry

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorAdapter437.port
#print axioms ShielddSecurity.VariableSelectorAdapter437.port

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorAdapter437.templateArithmetic
#print axioms ShielddSecurity.VariableSelectorAdapter437.templateArithmetic

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorAdapter437.expectedX
#print axioms ShielddSecurity.VariableSelectorAdapter437.expectedX

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorAdapter437.expectedY
#print axioms ShielddSecurity.VariableSelectorAdapter437.expectedY

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorAdapter437.Valid
#print axioms ShielddSecurity.VariableSelectorAdapter437.Valid

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorAdapter437.validDecidable
#print axioms ShielddSecurity.VariableSelectorAdapter437.validDecidable

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorAdapter437.check
#print axioms ShielddSecurity.VariableSelectorAdapter437.check

set_option pp.all true in
#check @ShielddSecurity.VariableSelectorAdapter437.coordinates
#print axioms ShielddSecurity.VariableSelectorAdapter437.coordinates
