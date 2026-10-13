import ShielddSecurity.VariableTraceBits446
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableTraceAccess452
open Group TransferOwnership
variable {F J : Type} [Field F] [AddCommGroup J]

def before (input : Point F) (windows : List (WindowWitness F)) (fallback : WindowWitness F) : Nat → Point F
  | 0 => input
  | index+1 => (windows[index]?.getD fallback).output

theorem before_cons (input : Point F) (head : WindowWitness F) (tail : List (WindowWitness F))
    (fallback : WindowWitness F) (index : Nat) :
    before input (head::tail) fallback (index+1)=before head.output tail fallback index := by
  cases index <;> rfl

theorem indexed_equations (d : F) (base twice triple input : Point F)
    (windows : List (WindowWitness F)) (fallback : WindowWitness F) (index : Nat)
    (bound : index<windows.length) (equations : TraceEquations d base twice triple input windows) :
    WindowEquations d base twice triple (before input windows fallback index) (windows[index]?.getD fallback) := by
  induction windows generalizing input index with
  | nil => simp at bound
  | cons head tail ih =>
    cases index with
    | zero => exact equations.1
    | succ index =>
      rw [before_cons,List.getElem?_cons_succ]
      exact ih head.output index (by simpa using bound) equations.2

theorem first_selection {d : F} (model : StandardCurveModel J d) (base : J)
    (head : Bool × Bool) (tail : List (Bool × Bool)) (fallback : WindowWitness F) :
    windowPoint (if head.1 then 1 else 0) (if head.2 then 1 else 0)
      (model.coordinates base) (model.coordinates (2 • base)) (model.coordinates (3 • base))=
    ((VariableTraceConstruction442.trace model base 0 (head::tail))[0]?.getD fallback).output := by
  rw [selected_coordinates]
  simp only [VariableTraceConstruction442.trace,List.getElem?_cons_zero,Option.getD_some,
    VariableTraceConstruction442.window,VariableTraceConstruction442.next,nsmul_zero,zero_add]
end ShielddSecurity.VariableTraceAccess452

set_option pp.all true in
#check @ShielddSecurity.VariableTraceAccess452.before
#print axioms ShielddSecurity.VariableTraceAccess452.before

set_option pp.all true in
#check @ShielddSecurity.VariableTraceAccess452.before_cons
#print axioms ShielddSecurity.VariableTraceAccess452.before_cons

set_option pp.all true in
#check @ShielddSecurity.VariableTraceAccess452.indexed_equations
#print axioms ShielddSecurity.VariableTraceAccess452.indexed_equations

set_option pp.all true in
#check @ShielddSecurity.VariableTraceAccess452.first_selection
#print axioms ShielddSecurity.VariableTraceAccess452.first_selection
