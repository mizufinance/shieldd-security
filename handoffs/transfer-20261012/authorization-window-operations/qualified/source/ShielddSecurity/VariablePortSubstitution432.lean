import ShielddSecurity.VariableDoubleTemplate431
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariablePortSubstitution432
open Compiler CompilerArithmeticTransport41

def linear (ports : Nat → Linear) (terms : Linear) : Linear :=
  terms.flatMap (fun term => scaleLinear term.2 (ports term.1))
def row (ports : Nat → Linear) (value : Row) : Row := ⟨linear ports value.a,linear ports value.b⟩
def rows (ports : Nat → Linear) (values : List Row) : List Row := values.map (row ports)

variable {F : Type} [Field F]
theorem eval_linear (ports : Nat → Linear) (rho : Nat → F) (terms : Linear) :
    eval rho (linear ports terms)=eval (fun port => eval rho (ports port)) terms := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
    simp only [linear,List.flatMap_cons,eval_append,eval_scale,eval]
    exact congrArg (fun tail => (term.2:F)*eval rho (ports term.1)+tail) ih

theorem satisfies_rows (ports : Nat → Linear) (rho : Nat → F) (values : List Row) :
    Satisfies rho (rows ports values) ↔ Satisfies (fun port => eval rho (ports port)) values := by
  constructor
  · intro sat value member
    have h := sat (row ports value) (List.mem_map.mpr ⟨value,member,rfl⟩)
    simpa only [row,eval_linear] using h
  · intro sat value member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    simpa only [row,eval_linear] using sat original present

variable [CharP F p]
theorem double_iff (ports : Nat → Linear) (rho : Nat → F)
    (one : eval rho (ports 0)=1)
    (arithmetic : Satisfies rho (rows ports VariableDoubleTemplate431.arithmeticRows)) :
    Satisfies rho (rows ports VariableDoubleTemplate431.assertionRows) ↔
    TransferOwnership.DoubleEquations ⟨eval rho (ports 1),eval rho (ports 2)⟩
      ⟨eval rho (ports 3),eval rho (ports 4)⟩ := by
  rw [satisfies_rows]
  exact VariableDoubleTemplate431.double_iff _ one ((satisfies_rows ports rho _).mp arithmetic)
end ShielddSecurity.VariablePortSubstitution432

set_option pp.all true in
#check @ShielddSecurity.VariablePortSubstitution432.linear
#print axioms ShielddSecurity.VariablePortSubstitution432.linear

set_option pp.all true in
#check @ShielddSecurity.VariablePortSubstitution432.row
#print axioms ShielddSecurity.VariablePortSubstitution432.row

set_option pp.all true in
#check @ShielddSecurity.VariablePortSubstitution432.rows
#print axioms ShielddSecurity.VariablePortSubstitution432.rows

set_option pp.all true in
#check @ShielddSecurity.VariablePortSubstitution432.eval_linear
#print axioms ShielddSecurity.VariablePortSubstitution432.eval_linear

set_option pp.all true in
#check @ShielddSecurity.VariablePortSubstitution432.satisfies_rows
#print axioms ShielddSecurity.VariablePortSubstitution432.satisfies_rows

set_option pp.all true in
#check @ShielddSecurity.VariablePortSubstitution432.double_iff
#print axioms ShielddSecurity.VariablePortSubstitution432.double_iff
