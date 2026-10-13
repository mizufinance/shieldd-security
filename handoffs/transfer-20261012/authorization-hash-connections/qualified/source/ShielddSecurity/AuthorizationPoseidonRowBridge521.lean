import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
import ShielddSecurity.AuthorizationPoseidonPhase517
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPoseidonRowBridge521
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def copyRow : Row := ⟨[(0,1),(copy,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
theorem copy_canonical : canonical p copyRow.a=canonical p [(0,1),(copy,-1)] := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem copy_satisfied (rho : Nat → F) (linked : rho copy=rho 0) :
    Satisfies rho [copyRow] := by
  intro row member
  have same : row=copyRow := by simpa only [List.mem_singleton] using member
  subst row
  have value := canonical_equal rho copyRow.a [(0,1),(copy,-1)] copy_canonical
  rw [value]
  simp [copyRow,eval,Square,linked]
theorem from_arithmetic (rows : List Row) (start length : Nat)
    (checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt start length rows=true)
    (inside : start+length ≤ 177954) (rho : Nat → F) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    Satisfies rho (rows++[copyRow]) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 start length rows checked inside rho arithmetic
  intro row member
  rcases List.mem_append.mp member with left|right
  · exact sat row left
  · exact copy_satisfied rho linked row right
end ShielddSecurity.AuthorizationPoseidonRowBridge521
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPoseidonRowBridge521.copy_canonical
#print axioms ShielddSecurity.AuthorizationPoseidonRowBridge521.copy_canonical
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPoseidonRowBridge521.copy_satisfied
#print axioms ShielddSecurity.AuthorizationPoseidonRowBridge521.copy_satisfied
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPoseidonRowBridge521.from_arithmetic
#print axioms ShielddSecurity.AuthorizationPoseidonRowBridge521.from_arithmetic
