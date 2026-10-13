import ShielddSecurity.VariableOperationAdapter434
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PointEqualityAdapter440
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
structure Entry where
  outputX : Linear
  outputY : Linear
  expectedX : Linear
  expectedY : Linear
  assertionStart : Nat
  assertionRows : List Row
def template (entry : Entry) : List Row :=
  [⟨subtract entry.outputX entry.expectedX,[]⟩,⟨subtract entry.outputY entry.expectedY,[]⟩]
def Valid (entry : Entry) : Prop :=
  CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+entry.assertionStart) 2 entry.assertionRows=true ∧
  entry.assertionStart+2≤22816 ∧
  VariableOperationAdapter434.covers (template entry) entry.assertionRows=true ∧
  VariableOperationAdapter434.covers entry.assertionRows (template entry)=true
noncomputable instance validDecidable (entry : Entry) : Decidable (Valid entry) := by
  unfold Valid
  infer_instance
noncomputable def check (entry : Entry) : Bool := decide (Valid entry)
variable {F : Type} [Field F] [CharP F p]
theorem equality_iff (entry : Entry) (checked : check entry=true) (rho : Nat → F) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+entry.assertionStart+i)) 2 ↔
    Group.Point.mk (eval rho entry.outputX) (eval rho entry.outputY)=
      Group.Point.mk (eval rho entry.expectedX) (eval rho entry.expectedY) := by
  have valid : Valid entry := of_decide_eq_true checked
  rcases valid with ⟨actual,inside,forward,reverse⟩
  have shapes : Satisfies rho entry.assertionRows ↔ Satisfies rho (template entry) :=
    ⟨transfer rho _ _ forward,transfer rho _ _ reverse⟩
  rw [←CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt
    (177954+entry.assertionStart) 2 entry.assertionRows actual rho,shapes]
  simp only [template,Satisfies,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,Group.Point.mk.injEq]
  simp only [show eval rho ([] : Linear)=0 from rfl,VariableDoubleTemplate431.equality_row]
end ShielddSecurity.PointEqualityAdapter440

set_option pp.all true in
#check @ShielddSecurity.PointEqualityAdapter440.Entry
#print axioms ShielddSecurity.PointEqualityAdapter440.Entry

set_option pp.all true in
#check @ShielddSecurity.PointEqualityAdapter440.template
#print axioms ShielddSecurity.PointEqualityAdapter440.template

set_option pp.all true in
#check @ShielddSecurity.PointEqualityAdapter440.Valid
#print axioms ShielddSecurity.PointEqualityAdapter440.Valid

set_option pp.all true in
#check @ShielddSecurity.PointEqualityAdapter440.validDecidable
#print axioms ShielddSecurity.PointEqualityAdapter440.validDecidable

set_option pp.all true in
#check @ShielddSecurity.PointEqualityAdapter440.check
#print axioms ShielddSecurity.PointEqualityAdapter440.check

set_option pp.all true in
#check @ShielddSecurity.PointEqualityAdapter440.equality_iff
#print axioms ShielddSecurity.PointEqualityAdapter440.equality_iff
