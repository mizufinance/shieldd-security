import ShielddSecurity.VariableWindowJoin443
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableWindowLayout447
open Compiler CompilerArithmeticTransport41
structure Family where
  baseX : Nat
  precomputeX : Nat
  assertionStart : Nat

def previous (family : Family) (window : Nat) : Nat := family.precomputeX+4+6*(window-1)
def ports (family : Family) (window : Nat) (e : VariableWindowJoin443.Entry) : List (Linear × Nat) :=
  let prev := previous family window
  [(VariableOperationAdapter434.port e.first 1,prev),
   (VariableOperationAdapter434.port e.first 2,prev+1),
   (VariableOperationAdapter434.port e.first 3,prev+2),
   (VariableOperationAdapter434.port e.first 4,prev+3),
   (VariableOperationAdapter434.port e.second 3,prev+4),
   (VariableOperationAdapter434.port e.second 4,prev+5),
   (VariableOperationAdapter434.port e.addition 5,prev+6),
   (VariableOperationAdapter434.port e.addition 6,prev+7),
   (VariableSelectorAdapter437.port e.selector 1,2250-2*window),
   (VariableSelectorAdapter437.port e.selector 2,2251-2*window),
   (VariableSelectorAdapter437.port e.selector 3,family.baseX),
   (VariableSelectorAdapter437.port e.selector 4,family.baseX+1),
   (VariableSelectorAdapter437.port e.selector 5,family.precomputeX),
   (VariableSelectorAdapter437.port e.selector 6,family.precomputeX+1),
   (VariableSelectorAdapter437.port e.selector 7,family.precomputeX+2),
   (VariableSelectorAdapter437.port e.selector 8,family.precomputeX+3)]

def Valid (family : Family) (window : Nat) (e : VariableWindowJoin443.Entry) : Prop :=
  1≤window ∧ window<126 ∧
  e.first.assertionStart=family.assertionStart+6+6*(window-1) ∧
  e.second.assertionStart=family.assertionStart+8+6*(window-1) ∧
  e.addition.assertionStart=family.assertionStart+10+6*(window-1) ∧
  (ports family window e).all (fun pair => decide (canonical p pair.1=canonical p [(pair.2,1)]))=true
noncomputable instance validDecidable (family : Family) (window : Nat) (e : VariableWindowJoin443.Entry) :
    Decidable (Valid family window e) := by
  unfold Valid;infer_instance
noncomputable def check (family : Family) (window : Nat) (e : VariableWindowJoin443.Entry) : Bool :=
  decide (Valid family window e)

variable {F : Type} [Field F] [CharP F p]
theorem value (family : Family) (window : Nat) (e : VariableWindowJoin443.Entry)
    (checked : check family window e=true) (rho : Nat → F) (terms : Linear) (column : Nat)
    (member : (terms,column)∈ports family window e) : eval rho terms=rho column := by
  have valid : Valid family window e := of_decide_eq_true checked
  have pair := of_decide_eq_true (List.all_eq_true.mp valid.2.2.2.2.2 (terms,column) member)
  have equal := canonical_equal rho terms [(column,1)] pair
  simpa only [eval,Int.cast_one,one_mul,add_zero] using equal

structure BoundEntry where
  family : Family
  window : Nat
  entry : VariableWindowJoin443.Entry
noncomputable def checkBound (e : BoundEntry) : Bool := check e.family e.window e.entry
end ShielddSecurity.VariableWindowLayout447

set_option pp.all true in
#check @ShielddSecurity.VariableWindowLayout447.Family
#print axioms ShielddSecurity.VariableWindowLayout447.Family

set_option pp.all true in
#check @ShielddSecurity.VariableWindowLayout447.previous
#print axioms ShielddSecurity.VariableWindowLayout447.previous

set_option pp.all true in
#check @ShielddSecurity.VariableWindowLayout447.ports
#print axioms ShielddSecurity.VariableWindowLayout447.ports

set_option pp.all true in
#check @ShielddSecurity.VariableWindowLayout447.Valid
#print axioms ShielddSecurity.VariableWindowLayout447.Valid

set_option pp.all true in
#check @ShielddSecurity.VariableWindowLayout447.validDecidable
#print axioms ShielddSecurity.VariableWindowLayout447.validDecidable

set_option pp.all true in
#check @ShielddSecurity.VariableWindowLayout447.check
#print axioms ShielddSecurity.VariableWindowLayout447.check

set_option pp.all true in
#check @ShielddSecurity.VariableWindowLayout447.value
#print axioms ShielddSecurity.VariableWindowLayout447.value

set_option pp.all true in
#check @ShielddSecurity.VariableWindowLayout447.BoundEntry
#print axioms ShielddSecurity.VariableWindowLayout447.BoundEntry

set_option pp.all true in
#check @ShielddSecurity.VariableWindowLayout447.checkBound
#print axioms ShielddSecurity.VariableWindowLayout447.checkBound
