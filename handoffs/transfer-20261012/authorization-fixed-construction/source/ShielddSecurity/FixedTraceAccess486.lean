import ShielddSecurity.FixedTraceConstruction478
import ShielddSecurity.VariableTraceBitIndex454
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedTraceAccess486
open Group GroupFixedWindows
variable {F J : Type} [Field F] [AddCommGroup J]

def before (input : Point F) (windows : List (FixedWindowWitness F)) (fallback : FixedWindowWitness F) : Nat → Point F
  | 0 => input
  | index+1 => (windows[index]?.getD fallback).output

def beforeBase (base : Point F) (windows : List (FixedWindowWitness F)) (fallback : FixedWindowWitness F) : Nat → Point F
  | 0 => base
  | index+1 => (windows[index]?.getD fallback).nextBase

theorem before_cons (input : Point F) (head : FixedWindowWitness F) (tail : List (FixedWindowWitness F))
    (fallback : FixedWindowWitness F) (index : Nat) :
    before input (head::tail) fallback (index+1)=before head.output tail fallback index := by
  cases index <;> rfl

theorem beforeBase_cons (base : Point F) (head : FixedWindowWitness F) (tail : List (FixedWindowWitness F))
    (fallback : FixedWindowWitness F) (index : Nat) :
    beforeBase base (head::tail) fallback (index+1)=beforeBase head.nextBase tail fallback index := by
  cases index <;> rfl

theorem indexed_equations (d : F) (base input : Point F)
    (windows : List (FixedWindowWitness F)) (fallback : FixedWindowWitness F) (index : Nat)
    (bound : index<windows.length) (equations : FixedTraceEquations d input base windows) :
    FixedWindowEquations d (before input windows fallback index)
      (beforeBase base windows fallback index) (windows[index]?.getD fallback) := by
  induction windows generalizing base input index with
  | nil => simp at bound
  | cons head tail ih =>
    cases index with
    | zero => exact equations.1
    | succ index =>
      rw [before_cons,beforeBase_cons,List.getElem?_cons_succ]
      exact ih head.nextBase head.output index (by simpa using bound) equations.2

theorem constructed_base {d : F} (model : StandardCurveModel J d) (base acc : J)
    (bits : List (Bool × Bool)) (fallback : FixedWindowWitness F) (index : Nat) (bound : index≤bits.length) :
    beforeBase (model.coordinates base) (FixedTraceConstruction478.trace model base acc bits) fallback index=
      model.coordinates (4^index • base) := by
  induction bits generalizing base acc index with
  | nil =>
    have zero : index=0 := by simpa using bound
    subst index
    simp only [beforeBase,pow_zero,one_nsmul]
  | cons head tail ih =>
    cases index with
    | zero => simp only [beforeBase,pow_zero,one_nsmul]
    | succ index =>
      rw [FixedTraceConstruction478.trace,beforeBase_cons]
      change beforeBase (model.coordinates (4 • base))
        (FixedTraceConstruction478.trace model (4 • base) (FixedTraceConstruction478.next base acc head) tail) fallback index=_
      rw [ih (4 • base) (FixedTraceConstruction478.next base acc head) index (by simpa using bound)]
      rw [pow_succ,mul_nsmul]
      rw [←mul_nsmul,←mul_nsmul,Nat.mul_comm]

theorem trace_bits {d : F} (model : StandardCurveModel J d) (base acc : J)
    (bits : List (Bool × Bool)) (fallback : FixedWindowWitness F) (index : Nat) (bound : index<bits.length) :
    let value := (FixedTraceConstruction478.trace model base acc bits)[index]?.getD fallback
    (value.low,value.high)=bits[index]?.getD (false,false) := by
  induction bits generalizing base acc index with
  | nil => simp at bound
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index =>
      exact ih (4 • base) (FixedTraceConstruction478.next base acc head) index (by simpa using bound)

theorem windows_bits {d : F} (model : StandardCurveModel J d) (base : J) (bits : List Bool)
    (length : bits.length=252) (fallback : FixedWindowWitness F) (index : Nat) (bound : index<126) :
    let value := (FixedTraceConstruction478.windows model base bits)[index]?.getD fallback
    (value.low,value.high)=(bits[2*index]?.getD false,bits[2*index+1]?.getD false) := by
  have pairLength : (VariableTraceBits446.pairs bits).length=126 := by rw [VariableTraceBits446.pairs_length,length]
  have result := trace_bits model base 0 (VariableTraceBits446.pairs bits) fallback index (by omega)
  rw [VariableTraceBitIndex454.pairs_get] at result
  exact result

theorem before_length (input : Point F) (windows : List (FixedWindowWitness F)) (fallback : FixedWindowWitness F) :
    before input windows fallback windows.length=fixedTraceOutput input windows := by
  induction windows generalizing input with
  | nil => rfl
  | cons head tail ih =>
    rw [List.length_cons,before_cons]
    exact ih head.output
end ShielddSecurity.FixedTraceAccess486

set_option pp.all true in
#check @ShielddSecurity.FixedTraceAccess486.before
#print axioms ShielddSecurity.FixedTraceAccess486.before

set_option pp.all true in
#check @ShielddSecurity.FixedTraceAccess486.beforeBase
#print axioms ShielddSecurity.FixedTraceAccess486.beforeBase

set_option pp.all true in
#check @ShielddSecurity.FixedTraceAccess486.before_cons
#print axioms ShielddSecurity.FixedTraceAccess486.before_cons

set_option pp.all true in
#check @ShielddSecurity.FixedTraceAccess486.beforeBase_cons
#print axioms ShielddSecurity.FixedTraceAccess486.beforeBase_cons

set_option pp.all true in
#check @ShielddSecurity.FixedTraceAccess486.indexed_equations
#print axioms ShielddSecurity.FixedTraceAccess486.indexed_equations

set_option pp.all true in
#check @ShielddSecurity.FixedTraceAccess486.constructed_base
#print axioms ShielddSecurity.FixedTraceAccess486.constructed_base

set_option pp.all true in
#check @ShielddSecurity.FixedTraceAccess486.trace_bits
#print axioms ShielddSecurity.FixedTraceAccess486.trace_bits

set_option pp.all true in
#check @ShielddSecurity.FixedTraceAccess486.windows_bits
#print axioms ShielddSecurity.FixedTraceAccess486.windows_bits

set_option pp.all true in
#check @ShielddSecurity.FixedTraceAccess486.before_length
#print axioms ShielddSecurity.FixedTraceAccess486.before_length
