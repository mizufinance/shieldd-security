import ShielddSecurity.AuthorizationPoseidonCapture518C56B0R01
import ShielddSecurity.AuthorizationPoseidonRowBridge521
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPrefixBindings527C56B0R01
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def arithmeticRows := AuthorizationPoseidonCapture518C56B0R01.rows.take 24
theorem actual : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 38060 24 arithmeticRows=true := by decide +kernel
theorem split : AuthorizationPoseidonCapture518C56B0R01.rows=arithmeticRows++[AuthorizationPoseidonRowBridge521.copyRow] := by decide +kernel
theorem arbitrary_round {F : Type} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (AuthorizationPoseidonCapture518C56B0R01.after i))=Poseidon.round (Poseidon.castParameters AuthorizationPoseidonCapture518C56B0R01.parameters) 1
      (fun i => eval rho (AuthorizationPoseidonCapture518C56B0R01.before i)) := by
  apply AuthorizationPoseidonCapture518C56B0R01.arbitrary_round rho one
  rw [split]
  exact AuthorizationPoseidonRowBridge521.from_arithmetic arithmeticRows 38060 24 actual (by decide) rho linked arithmetic
end ShielddSecurity.AuthorizationPrefixBindings527C56B0R01
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPrefixBindings527C56B0R01.actual
#print axioms ShielddSecurity.AuthorizationPrefixBindings527C56B0R01.actual
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPrefixBindings527C56B0R01.split
#print axioms ShielddSecurity.AuthorizationPrefixBindings527C56B0R01.split
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPrefixBindings527C56B0R01.arbitrary_round
#print axioms ShielddSecurity.AuthorizationPrefixBindings527C56B0R01.arbitrary_round
