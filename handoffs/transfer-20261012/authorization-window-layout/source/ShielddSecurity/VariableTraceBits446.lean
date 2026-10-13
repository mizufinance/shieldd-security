import ShielddSecurity.VariableTraceConstruction442
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableTraceBits446
open Group TransferOwnership

def pairs : List Bool → List (Bool × Bool)
  | [] => []
  | [low] => [(low,false)]
  | low::high::rest => (low,high)::pairs rest

theorem digits (bits : List Bool) :
    (pairs bits).map (fun b => b.1.toNat+2*b.2.toNat)=TransferWindows.pairDigits bits := by
  match bits with
  | [] => rfl
  | [low] => cases low <;> rfl
  | low::high::rest =>
    simp only [pairs,List.map_cons,TransferWindows.pairDigits,digits rest]
    cases low <;> cases high <;> rfl
termination_by structural bits

theorem pairs_length (bits : List Bool) : (pairs bits).length=(bits.length+1)/2 := by
  match bits with
  | [] => rfl
  | [low] => simp [pairs]
  | low::high::rest =>
    simp only [pairs,List.length_cons,pairs_length rest]
    omega
termination_by structural bits

variable {F J : Type} [Field F] [AddCommGroup J]
def windows {d : F} (model : StandardCurveModel J d) (base : J) (bits : List Bool) : List (WindowWitness F) :=
  VariableTraceConstruction442.trace model base 0 (pairs bits).reverse

theorem trace_length {d : F} (model : StandardCurveModel J d) (base acc : J)
    (bits : List (Bool × Bool)) : (VariableTraceConstruction442.trace model base acc bits).length=bits.length := by
  induction bits generalizing acc with
  | nil => rfl
  | cons head tail ih => simp only [VariableTraceConstruction442.trace,List.length_cons,ih]

theorem windows_length {d : F} (model : StandardCurveModel J d) (base : J) (bits : List Bool) :
    (windows model base bits).length=(bits.length+1)/2 := by
  rw [windows,trace_length,List.length_reverse,pairs_length]

theorem order {d : F} (model : StandardCurveModel J d) (base : J) (bits : List Bool) :
    (windows model base bits).map (fun w => w.low.toNat+2*w.high.toNat)=
      (TransferWindows.pairDigits bits).reverse := by
  rw [windows,VariableTraceConstruction442.digits,List.map_reverse,digits]

variable (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
variable (imaginarySquare : imaginary*imaginary = -1)
include imaginary nonSquare imaginarySquare

theorem equations (base : J) (bits : List Bool) :
    TraceEquations d (model.coordinates base) (model.coordinates (2 • base))
      (model.coordinates (3 • base)) (model.coordinates 0) (windows model base bits) :=
  VariableTraceConstruction442.trace_equations d imaginary model nonSquare imaginarySquare base 0 (pairs bits).reverse

theorem output (base : J) (bits : List Bool) :
    traceOutput (model.coordinates 0) (windows model base bits)=
      model.coordinates (ShielddSecurity.binary bits • base) := by
  have double := VariableGroupCompletion439.double_equations d imaginary model nonSquare imaginarySquare base
  have add := VariableGroupCompletion439.add_equations d imaginary model nonSquare imaginarySquare (2 • base) base
  have three : 2 • base+base=3 • base := by
    simp only [show (3:Nat)=2+1 from rfl,add_nsmul,one_nsmul]
  rw [three] at add
  exact trace_scalar_coordinates d imaginary model nonSquare imaginarySquare base _ _ double add
    (windows model base bits) bits (order model base bits) (equations d imaginary model nonSquare imaginarySquare base bits)

theorem encoded_output (base : J) (width scalar : Nat) (bound : scalar<2^width) :
    traceOutput (model.coordinates 0) (windows model base (encodeBits width scalar))=
      model.coordinates (scalar • base) := by
  rw [output d imaginary model nonSquare imaginarySquare,encodeBits_value width scalar bound]
end ShielddSecurity.VariableTraceBits446

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBits446.pairs
#print axioms ShielddSecurity.VariableTraceBits446.pairs

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBits446.digits
#print axioms ShielddSecurity.VariableTraceBits446.digits

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBits446.windows
#print axioms ShielddSecurity.VariableTraceBits446.windows

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBits446.order
#print axioms ShielddSecurity.VariableTraceBits446.order

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBits446.equations
#print axioms ShielddSecurity.VariableTraceBits446.equations

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBits446.output
#print axioms ShielddSecurity.VariableTraceBits446.output

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBits446.encoded_output
#print axioms ShielddSecurity.VariableTraceBits446.encoded_output

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBits446.pairs_length
#print axioms ShielddSecurity.VariableTraceBits446.pairs_length

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBits446.trace_length
#print axioms ShielddSecurity.VariableTraceBits446.trace_length

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBits446.windows_length
#print axioms ShielddSecurity.VariableTraceBits446.windows_length
