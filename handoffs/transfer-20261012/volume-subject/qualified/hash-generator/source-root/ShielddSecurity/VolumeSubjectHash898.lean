/- Generated from maintained volume subject-hash template. -/
import ShielddSecurity.VolumeSubjectHashPermutation897
import ShielddSecurity.VolumeSubjectHashCapture893
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeSubjectHash898
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def parameters := VolumeSubjectHashPermutation897.parameters
noncomputable def result := VolumeSubjectHashPermutation897.result
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt

theorem initial (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho (VolumeSubjectHashPermutation897.before i))=
      Poseidon.absorb (Poseidon.initial 4 5) [rho 1504,rho 1505,rho 1512,rho 1513,rho 6] := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [VolumeSubjectHashPermutation897.before,VolumeSubjectHashCapture893C123B0R00.before,
      Poseidon.absorb,Poseidon.initial,eval,one,Fin.val_ofNat]
  · change eval rho [(1512,1)]=rho 1512
    simp [eval]
  · change eval rho [(1513,1)]=rho 1513
    simp [eval]
  · change eval rho [(6,1)]=rho 6
    simp [eval]

theorem hash (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.hash6 (Poseidon.castParameters parameters) 4 [rho 1504,rho 1505,rho 1512,rho 1513,rho 6] := by
  have permutation := VolumeSubjectHashPermutation897.permutation rho one linked arithmetic
  rw [initial rho one] at permutation
  have joined := Poseidon.hash6_of_one_block (Poseidon.castParameters parameters) 4 [rho 1504,rho 1505,rho 1512,rho 1513,rho 6]
    (Poseidon.initial 4 5) (fun i => eval rho (VolumeSubjectHashPermutation897.after i)) rfl rfl permutation
  simpa only [VolumeSubjectHashPermutation897.result_port,result] using joined
end ShielddSecurity.VolumeSubjectHash898

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHash898.initial
#print axioms ShielddSecurity.VolumeSubjectHash898.initial

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHash898.hash
#print axioms ShielddSecurity.VolumeSubjectHash898.hash
