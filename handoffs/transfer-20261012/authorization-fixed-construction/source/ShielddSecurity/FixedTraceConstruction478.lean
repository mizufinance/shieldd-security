import ShielddSecurity.VariableTraceBits446
import ShielddSecurity.GroupFixedWindows
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedTraceConstruction478
open Group GroupFixedWindows
variable {F J : Type} [Field F] [AddCommGroup J]

def next (base acc : J) (bits : Bool × Bool) : J :=
  acc+(bits.1.toNat+2*bits.2.toNat) • base

def window {d : F} (model : StandardCurveModel J d) (base acc : J)
    (bits : Bool × Bool) : FixedWindowWitness F :=
  ⟨bits.1,bits.2,model.coordinates (2 • base),model.coordinates (3 • base),
    model.coordinates (4 • base),model.coordinates (next base acc bits)⟩

def trace {d : F} (model : StandardCurveModel J d) : J → J → List (Bool × Bool) → List (FixedWindowWitness F)
  | _,_,[] => []
  | base,acc,bits::tail => window model base acc bits :: trace model (4 • base) (next base acc bits) tail

variable (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
variable (imaginarySquare : imaginary*imaginary = -1)

include imaginary nonSquare imaginarySquare

theorem window_equations (base acc : J) (bits : Bool × Bool) :
    FixedWindowEquations d (model.coordinates acc) (model.coordinates base) (window model base acc bits) := by
  have twice : 2 • base=base+base := two_nsmul base
  have triple : 3 • base=2 • base+base := by
    simp only [show (3:Nat)=2+1 from rfl,add_nsmul,one_nsmul]
  have four : 4 • base=2 • base+2 • base := by rw [←add_nsmul]
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · change model.coordinates (2 • base)=nativeAdd d (model.coordinates base) (model.coordinates base)
    rw [native_add_coordinates d imaginary model nonSquare imaginarySquare,twice]
  · change model.coordinates (3 • base)=nativeAdd d (model.coordinates (2 • base)) (model.coordinates base)
    rw [native_add_coordinates d imaginary model nonSquare imaginarySquare,triple]
  · change model.coordinates (4 • base)=nativeAdd d (model.coordinates (2 • base)) (model.coordinates (2 • base))
    rw [native_add_coordinates d imaginary model nonSquare imaginarySquare,four]
  · change TransferOwnership.AddEquations d (model.coordinates acc)
      (windowPoint (if bits.1 then 1 else 0) (if bits.2 then 1 else 0)
        (model.coordinates base) (model.coordinates (2 • base)) (model.coordinates (3 • base)))
      (model.coordinates (next base acc bits))
    rw [TransferOwnership.selected_coordinates]
    exact VariableGroupCompletion439.add_equations d imaginary model nonSquare imaginarySquare
      acc ((bits.1.toNat+2*bits.2.toNat) • base)

theorem trace_equations (base acc : J) (bits : List (Bool × Bool)) :
    FixedTraceEquations d (model.coordinates acc) (model.coordinates base) (trace model base acc bits) := by
  induction bits generalizing base acc with
  | nil => trivial
  | cons head tail ih =>
    exact ⟨window_equations d imaginary model nonSquare imaginarySquare base acc head,
      ih (4 • base) (next base acc head)⟩

omit imaginary nonSquare imaginarySquare

theorem digits {d : F} (model : StandardCurveModel J d) (base acc : J) (bits : List (Bool × Bool)) :
    (trace model base acc bits).map fixedDigit=bits.map (fun b => b.1.toNat+2*b.2.toNat) := by
  induction bits generalizing base acc with
  | nil => rfl
  | cons head tail ih => simp only [trace,List.map_cons,fixedDigit,window,ih]

theorem trace_length {d : F} (model : StandardCurveModel J d) (base acc : J) (bits : List (Bool × Bool)) :
    (trace model base acc bits).length=bits.length := by
  induction bits generalizing base acc with
  | nil => rfl
  | cons head tail ih => simp only [trace,List.length_cons,ih]

def windows {d : F} (model : StandardCurveModel J d) (base : J) (bits : List Bool) : List (FixedWindowWitness F) :=
  trace model base 0 (VariableTraceBits446.pairs bits)

include imaginary nonSquare imaginarySquare

theorem output (base : J) (bits : List Bool) :
    fixedTraceOutput (model.coordinates 0) (windows model base bits)=model.coordinates (ShielddSecurity.binary bits • base) := by
  apply fixed_trace_scalar_coordinates d imaginary model nonSquare imaginarySquare base _ bits
  · exact (digits model base 0 (VariableTraceBits446.pairs bits)).trans (VariableTraceBits446.digits bits)
  · exact trace_equations d imaginary model nonSquare imaginarySquare base 0 (VariableTraceBits446.pairs bits)

theorem encoded_output (base : J) (width scalar : Nat) (bound : scalar<2^width) :
    fixedTraceOutput (model.coordinates 0) (windows model base (encodeBits width scalar))=model.coordinates (scalar • base) := by
  rw [output d imaginary model nonSquare imaginarySquare,encodeBits_value width scalar bound]
end ShielddSecurity.FixedTraceConstruction478

set_option pp.all true in
#check @ShielddSecurity.FixedTraceConstruction478.next
#print axioms ShielddSecurity.FixedTraceConstruction478.next

set_option pp.all true in
#check @ShielddSecurity.FixedTraceConstruction478.window
#print axioms ShielddSecurity.FixedTraceConstruction478.window

set_option pp.all true in
#check @ShielddSecurity.FixedTraceConstruction478.trace
#print axioms ShielddSecurity.FixedTraceConstruction478.trace

set_option pp.all true in
#check @ShielddSecurity.FixedTraceConstruction478.window_equations
#print axioms ShielddSecurity.FixedTraceConstruction478.window_equations

set_option pp.all true in
#check @ShielddSecurity.FixedTraceConstruction478.trace_equations
#print axioms ShielddSecurity.FixedTraceConstruction478.trace_equations

set_option pp.all true in
#check @ShielddSecurity.FixedTraceConstruction478.digits
#print axioms ShielddSecurity.FixedTraceConstruction478.digits

set_option pp.all true in
#check @ShielddSecurity.FixedTraceConstruction478.trace_length
#print axioms ShielddSecurity.FixedTraceConstruction478.trace_length

set_option pp.all true in
#check @ShielddSecurity.FixedTraceConstruction478.windows
#print axioms ShielddSecurity.FixedTraceConstruction478.windows

set_option pp.all true in
#check @ShielddSecurity.FixedTraceConstruction478.output
#print axioms ShielddSecurity.FixedTraceConstruction478.output

set_option pp.all true in
#check @ShielddSecurity.FixedTraceConstruction478.encoded_output
#print axioms ShielddSecurity.FixedTraceConstruction478.encoded_output
