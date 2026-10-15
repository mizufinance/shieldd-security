/- Generated from maintained user path-hash generator; edit generator or templates. -/
import ShielddSecurity.UserPathHashCapture953C33B0R00
import ShielddSecurity.AuthorizationPoseidonRowBridge521
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathHashPrefix954C33B0R00
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def arithmeticRows := UserPathHashCapture953C33B0R00.rows.take 16
theorem actual : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 16780 16 arithmeticRows=true := by decide +kernel
theorem split : UserPathHashCapture953C33B0R00.rows=arithmeticRows++[AuthorizationPoseidonRowBridge521.copyRow] := by decide +kernel
theorem arbitrary_round {F : Type} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (UserPathHashCapture953C33B0R00.after i))=Poseidon.round (Poseidon.castParameters UserPathHashCapture953C33B0R00.parameters) 0
      (fun i => eval rho (UserPathHashCapture953C33B0R00.before i)) := by
  apply UserPathHashCapture953C33B0R00.arbitrary_round rho one
  rw [split]
  exact AuthorizationPoseidonRowBridge521.from_arithmetic arithmeticRows 16780 16 actual (by decide) rho linked arithmetic
end ShielddSecurity.UserPathHashPrefix954C33B0R00
set_option pp.all true in
#check @ShielddSecurity.UserPathHashPrefix954C33B0R00.actual
#print axioms ShielddSecurity.UserPathHashPrefix954C33B0R00.actual
set_option pp.all true in
#check @ShielddSecurity.UserPathHashPrefix954C33B0R00.split
#print axioms ShielddSecurity.UserPathHashPrefix954C33B0R00.split
set_option pp.all true in
#check @ShielddSecurity.UserPathHashPrefix954C33B0R00.arbitrary_round
#print axioms ShielddSecurity.UserPathHashPrefix954C33B0R00.arbitrary_round
