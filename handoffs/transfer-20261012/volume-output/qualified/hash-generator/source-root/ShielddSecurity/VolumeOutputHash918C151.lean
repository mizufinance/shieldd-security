/- Generated from maintained volume output-hash generator; edit generator or templates. -/
import ShielddSecurity.VolumeOutputHashPermutation917C151
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeOutputHash918C151
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def parameters := VolumeOutputHashPermutation917C151.parameters
noncomputable def result := VolumeOutputHashPermutation917C151.result
noncomputable def inputs : List Linear := [[(7740,1)],[(7739,1)],[(7742,1)],[(8508,1)]]
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
theorem initial (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho (VolumeOutputHashPermutation917C151.before i))=Poseidon.absorb (Poseidon.initial 5 4) (inputs.map (eval rho)) := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho [(0,1029)]=((1029:Nat):F)
    norm_num [eval,one]
  · change eval rho [(7740,1)]=0+eval rho [(7740,1)]
    exact (zero_add _).symm
  · change eval rho [(7739,1)]=0+eval rho [(7739,1)]
    exact (zero_add _).symm
  · change eval rho [(7742,1)]=0+eval rho [(7742,1)]
    exact (zero_add _).symm
  · change eval rho [(8508,1)]=0+eval rho [(8508,1)]
    exact (zero_add _).symm
  · change (0:F)=0+0
    exact (add_zero _).symm
theorem hash (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.hash6 (Poseidon.castParameters parameters) 5 (inputs.map (eval rho)) := by
  have permutation := VolumeOutputHashPermutation917C151.permutation rho one linked arithmetic
  rw [initial rho one] at permutation
  have joined := Poseidon.hash6_of_one_block (Poseidon.castParameters parameters) 5 (inputs.map (eval rho))
    (Poseidon.initial 5 4) (fun i => eval rho (VolumeOutputHashPermutation917C151.after i)) rfl rfl permutation
  simpa only [VolumeOutputHashPermutation917C151.result_port,result] using joined
end ShielddSecurity.VolumeOutputHash918C151

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHash918C151.initial
#print axioms ShielddSecurity.VolumeOutputHash918C151.initial

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHash918C151.hash
#print axioms ShielddSecurity.VolumeOutputHash918C151.hash
