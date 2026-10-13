import ShielddSecurity.VariableTraceBits446
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableTraceBitIndex454
open Group TransferOwnership

theorem pairs_get (bits : List Bool) (index : Nat) :
    ((VariableTraceBits446.pairs bits)[index]?.getD (false,false))=
      (bits[2*index]?.getD false,bits[2*index+1]?.getD false) := by
  match bits,index with
  | [],index => simp [VariableTraceBits446.pairs]
  | [low],0 => simp [VariableTraceBits446.pairs]
  | [low],index+1 => simp [VariableTraceBits446.pairs,Nat.mul_add,Nat.add_assoc]
  | low::high::rest,0 => rfl
  | low::high::rest,index+1 =>
    simpa [VariableTraceBits446.pairs,Nat.mul_add,Nat.add_assoc] using pairs_get rest index
termination_by structural bits

variable {F J : Type} [Field F] [AddCommGroup J]
theorem trace_bits {d : F} (model : StandardCurveModel J d) (base acc : J)
    (bits : List (Bool × Bool)) (fallback : WindowWitness F) (index : Nat) (bound : index<bits.length) :
    let value := (VariableTraceConstruction442.trace model base acc bits)[index]?.getD fallback
    (value.low,value.high)=bits[index]?.getD (false,false) := by
  induction bits generalizing acc index with
  | nil => simp at bound
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index =>
      exact ih (VariableTraceConstruction442.next base acc head) index (by simpa using bound)

theorem windows_bits {d : F} (model : StandardCurveModel J d) (base : J) (bits : List Bool)
    (length : bits.length=252) (fallback : WindowWitness F) (index : Nat) (bound : index<126) :
    let value := (VariableTraceBits446.windows model base bits)[index]?.getD fallback
    (value.low,value.high)=
      (bits[250-2*index]?.getD false,bits[251-2*index]?.getD false) := by
  have pairLength : (VariableTraceBits446.pairs bits).length=126 := by rw [VariableTraceBits446.pairs_length,length]
  have inPairs : index<(VariableTraceBits446.pairs bits).length := by omega
  have result := trace_bits model base 0 (VariableTraceBits446.pairs bits).reverse fallback index
    (by simpa only [List.length_reverse] using inPairs)
  rw [List.getElem?_reverse inPairs,pairLength,pairs_get] at result
  have low : 2*(126-1-index)=250-2*index := by omega
  have high : 250-2*index+1=251-2*index := by omega
  simpa only [VariableTraceBits446.windows,low,high] using result
end ShielddSecurity.VariableTraceBitIndex454

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBitIndex454.pairs_get
#print axioms ShielddSecurity.VariableTraceBitIndex454.pairs_get

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBitIndex454.trace_bits
#print axioms ShielddSecurity.VariableTraceBitIndex454.trace_bits

set_option pp.all true in
#check @ShielddSecurity.VariableTraceBitIndex454.windows_bits
#print axioms ShielddSecurity.VariableTraceBitIndex454.windows_bits
