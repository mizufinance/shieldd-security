/- Generated from maintained public statement-hash generator; edit generator or templates. -/
import ShielddSecurity.PublicStatementHashCapture972C187B5R00
import ShielddSecurity.AuthorizationPoseidonRowBridge521
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublicStatementHashPrefix973C187B5R00
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def arithmeticRows := PublicStatementHashCapture972C187B5R00.rows.take 24
theorem actual : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 174594 24 arithmeticRows=true := by decide +kernel
theorem split : PublicStatementHashCapture972C187B5R00.rows=arithmeticRows++[AuthorizationPoseidonRowBridge521.copyRow] := by decide +kernel
theorem arbitrary_round {F : Type} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (PublicStatementHashCapture972C187B5R00.after i))=Poseidon.round (Poseidon.castParameters PublicStatementHashCapture972C187B5R00.parameters) 0
      (fun i => eval rho (PublicStatementHashCapture972C187B5R00.before i)) := by
  apply PublicStatementHashCapture972C187B5R00.arbitrary_round rho one
  rw [split]
  exact AuthorizationPoseidonRowBridge521.from_arithmetic arithmeticRows 174594 24 actual (by decide) rho linked arithmetic
end ShielddSecurity.PublicStatementHashPrefix973C187B5R00
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashPrefix973C187B5R00.actual
#print axioms ShielddSecurity.PublicStatementHashPrefix973C187B5R00.actual
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashPrefix973C187B5R00.split
#print axioms ShielddSecurity.PublicStatementHashPrefix973C187B5R00.split
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashPrefix973C187B5R00.arbitrary_round
#print axioms ShielddSecurity.PublicStatementHashPrefix973C187B5R00.arbitrary_round
