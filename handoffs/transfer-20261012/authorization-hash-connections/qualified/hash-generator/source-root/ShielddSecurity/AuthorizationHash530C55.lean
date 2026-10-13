import ShielddSecurity.AuthorizationPermutation529C55B0
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationHash530C55
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def inputs : List Linear := [[(1993,1)],[(1980,1)],[(1981,1)]]
def result := AuthorizationPermutation529C55B0.result
def parameters := AuthorizationPermutation529C55B0.parameters
variable {F : Type} [Field F] [CharP F p]
def values (rho : Nat → F) := inputs.map (eval rho)
theorem initial (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho (AuthorizationPermutation529C55B0.before i))=
      Poseidon.absorb (Poseidon.initial 16 3) (values rho) := by
  funext i
  have cases : i=⟨0,by decide⟩ ∨ i=⟨1,by decide⟩ ∨ i=⟨2,by decide⟩ ∨ i=⟨3,by decide⟩ ∨ i=⟨4,by decide⟩ ∨ i=⟨5,by decide⟩ := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [AuthorizationPermutation529C55B0.before,AuthorizationPoseidonCapture518C55B0R00.before,
      Poseidon.absorb,Poseidon.initial,values,inputs,eval,one,Fin.val_ofNat]
theorem hash (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.hash6 (Poseidon.castParameters parameters) 16 (values rho) := by
  have out := AuthorizationPermutation529C55B0.output rho one linked arithmetic
  rw [initial rho one] at out
  exact out
end ShielddSecurity.AuthorizationHash530C55
set_option pp.all true in
#check @ShielddSecurity.AuthorizationHash530C55.initial
#print axioms ShielddSecurity.AuthorizationHash530C55.initial
set_option pp.all true in
#check @ShielddSecurity.AuthorizationHash530C55.hash
#print axioms ShielddSecurity.AuthorizationHash530C55.hash
