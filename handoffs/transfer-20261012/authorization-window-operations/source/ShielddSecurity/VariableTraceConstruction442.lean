import ShielddSecurity.VariableGroupCompletion439
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableTraceConstruction442
open Group TransferOwnership
variable {F J : Type} [Field F] [AddCommGroup J]

def next (base acc : J) (bits : Bool × Bool) : J :=
  2 • (2 • acc)+(bits.1.toNat+2*bits.2.toNat) • base

def window {d : F} (model : StandardCurveModel J d) (base acc : J)
    (bits : Bool × Bool) : WindowWitness F :=
  ⟨bits.1,bits.2,model.coordinates (2 • acc),model.coordinates (2 • (2 • acc)),
    model.coordinates (next base acc bits)⟩

def trace {d : F} (model : StandardCurveModel J d) (base : J) : J → List (Bool × Bool) → List (WindowWitness F)
  | _,[] => []
  | acc,bits::tail => window model base acc bits :: trace model base (next base acc bits) tail

variable (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
variable (imaginarySquare : imaginary*imaginary = -1)
include imaginary nonSquare imaginarySquare

theorem window_equations (base acc : J) (bits : Bool × Bool) :
    WindowEquations d (model.coordinates base) (model.coordinates (2 • base))
      (model.coordinates (3 • base)) (model.coordinates acc) (window model base acc bits) := by
  refine ⟨VariableGroupCompletion439.double_equations d imaginary model nonSquare imaginarySquare acc,
    VariableGroupCompletion439.double_equations d imaginary model nonSquare imaginarySquare (2 • acc),?_⟩
  change AddEquations d (model.coordinates (2 • (2 • acc)))
    (windowPoint (if bits.1 then 1 else 0) (if bits.2 then 1 else 0)
      (model.coordinates base) (model.coordinates (2 • base)) (model.coordinates (3 • base)))
    (model.coordinates (next base acc bits))
  rw [selected_coordinates]
  exact VariableGroupCompletion439.add_equations d imaginary model nonSquare imaginarySquare
    (2 • (2 • acc)) ((bits.1.toNat+2*bits.2.toNat) • base)

theorem trace_equations (base acc : J) (bits : List (Bool × Bool)) :
    TraceEquations d (model.coordinates base) (model.coordinates (2 • base))
      (model.coordinates (3 • base)) (model.coordinates acc) (trace model base acc bits) := by
  induction bits generalizing acc with
  | nil => trivial
  | cons head tail ih =>
    exact ⟨window_equations d imaginary model nonSquare imaginarySquare base acc head,
      ih (next base acc head)⟩

omit imaginary nonSquare imaginarySquare in
theorem digits {d : F} (model : StandardCurveModel J d) (base acc : J)
    (bits : List (Bool × Bool)) :
    (trace model base acc bits).map (fun w => w.low.toNat+2*w.high.toNat)=
      bits.map (fun b => b.1.toNat+2*b.2.toNat) := by
  induction bits generalizing acc with
  | nil => rfl
  | cons head tail ih =>
    simp only [trace,List.map_cons,window,ih]
end ShielddSecurity.VariableTraceConstruction442

set_option pp.all true in
#check @ShielddSecurity.VariableTraceConstruction442.next
#print axioms ShielddSecurity.VariableTraceConstruction442.next

set_option pp.all true in
#check @ShielddSecurity.VariableTraceConstruction442.window
#print axioms ShielddSecurity.VariableTraceConstruction442.window

set_option pp.all true in
#check @ShielddSecurity.VariableTraceConstruction442.trace
#print axioms ShielddSecurity.VariableTraceConstruction442.trace

set_option pp.all true in
#check @ShielddSecurity.VariableTraceConstruction442.window_equations
#print axioms ShielddSecurity.VariableTraceConstruction442.window_equations

set_option pp.all true in
#check @ShielddSecurity.VariableTraceConstruction442.trace_equations
#print axioms ShielddSecurity.VariableTraceConstruction442.trace_equations

set_option pp.all true in
#check @ShielddSecurity.VariableTraceConstruction442.digits
#print axioms ShielddSecurity.VariableTraceConstruction442.digits
