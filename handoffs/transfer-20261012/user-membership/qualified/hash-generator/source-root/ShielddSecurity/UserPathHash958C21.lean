/- Generated from maintained user path-hash generator; edit generator or templates. -/
import ShielddSecurity.UserPathHashPermutation957C21B0
import ShielddSecurity.UserPathHashPermutation957C21B1
import ShielddSecurity.WideHashTwoBlocks960
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathHash958C21
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def parameters := UserPathHashPermutation957C21B0.parameters
noncomputable def result := UserPathHashPermutation957C21B1.result
noncomputable def inputs : List Linear := [[(1504,1)],[(1505,1)],[(1512,1)],[(1513,1)],[(6,1)],[(1520,1)],[(1521,1)],[(1528,1)],[(1529,1)]]
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
theorem initial (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho (UserPathHashPermutation957C21B0.before i))=Poseidon.absorb (Poseidon.initial 19 9) ((inputs.map (eval rho)).take 5) := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho [(0,2323)]=((2323:Nat):F)
    norm_num [eval,one]
  · change eval rho [(1504,1)]=0+eval rho [(1504,1)]
    exact (zero_add _).symm
  · change eval rho [(1505,1)]=0+eval rho [(1505,1)]
    exact (zero_add _).symm
  · change eval rho [(1512,1)]=0+eval rho [(1512,1)]
    exact (zero_add _).symm
  · change eval rho [(1513,1)]=0+eval rho [(1513,1)]
    exact (zero_add _).symm
  · change eval rho [(6,1)]=0+eval rho [(6,1)]
    exact (zero_add _).symm
theorem continuation0_shape : canonical p (UserPathHashPermutation957C21B1.before 0)=canonical p (UserPathHashPermutation957C21B0.after 0) := by decide +kernel
theorem continuation1_shape : canonical p (UserPathHashPermutation957C21B1.before 1)=canonical p (UserPathHashPermutation957C21B0.after 1++[(1520,1)]) := by decide +kernel
theorem continuation2_shape : canonical p (UserPathHashPermutation957C21B1.before 2)=canonical p (UserPathHashPermutation957C21B0.after 2++[(1521,1)]) := by decide +kernel
theorem continuation3_shape : canonical p (UserPathHashPermutation957C21B1.before 3)=canonical p (UserPathHashPermutation957C21B0.after 3++[(1528,1)]) := by decide +kernel
theorem continuation4_shape : canonical p (UserPathHashPermutation957C21B1.before 4)=canonical p (UserPathHashPermutation957C21B0.after 4++[(1529,1)]) := by decide +kernel
theorem continuation5_shape : canonical p (UserPathHashPermutation957C21B1.before 5)=canonical p (UserPathHashPermutation957C21B0.after 5) := by decide +kernel
theorem continuation (rho : Nat → F) :
    (fun i => eval rho (UserPathHashPermutation957C21B1.before i))=Poseidon.absorb (fun i => eval rho (UserPathHashPermutation957C21B0.after i)) ((inputs.map (eval rho)).drop 5) := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho (UserPathHashPermutation957C21B1.before 0)=eval rho (UserPathHashPermutation957C21B0.after 0)
    exact canonical_equal rho _ _ continuation0_shape
  · change eval rho (UserPathHashPermutation957C21B1.before 1)=eval rho (UserPathHashPermutation957C21B0.after 1)+eval rho [(1520,1)]
    rw [canonical_equal rho _ _ continuation1_shape,eval_append]
  · change eval rho (UserPathHashPermutation957C21B1.before 2)=eval rho (UserPathHashPermutation957C21B0.after 2)+eval rho [(1521,1)]
    rw [canonical_equal rho _ _ continuation2_shape,eval_append]
  · change eval rho (UserPathHashPermutation957C21B1.before 3)=eval rho (UserPathHashPermutation957C21B0.after 3)+eval rho [(1528,1)]
    rw [canonical_equal rho _ _ continuation3_shape,eval_append]
  · change eval rho (UserPathHashPermutation957C21B1.before 4)=eval rho (UserPathHashPermutation957C21B0.after 4)+eval rho [(1529,1)]
    rw [canonical_equal rho _ _ continuation4_shape,eval_append]
  · change eval rho (UserPathHashPermutation957C21B1.before 5)=eval rho (UserPathHashPermutation957C21B0.after 5)+0
    rw [canonical_equal rho _ _ continuation5_shape,add_zero]
theorem hash (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.hash6 (Poseidon.castParameters parameters) 19 (inputs.map (eval rho)) := by
  have first := UserPathHashPermutation957C21B0.permutation rho one linked arithmetic
  rw [initial rho one] at first
  have second := UserPathHashPermutation957C21B1.permutation rho one linked arithmetic
  rw [continuation rho] at second
  have joined := WideHashTwoBlocks960.hash (Poseidon.castParameters parameters) 19 (inputs.map (eval rho))
    ((inputs.map (eval rho)).take 5) ((inputs.map (eval rho)).drop 5) (Poseidon.initial 19 9)
    (fun i => eval rho (UserPathHashPermutation957C21B0.after i)) (fun i => eval rho (UserPathHashPermutation957C21B1.after i)) rfl rfl first second
  simpa only [UserPathHashPermutation957C21B1.result_port,result] using joined
end ShielddSecurity.UserPathHash958C21

set_option pp.all true in
#check @ShielddSecurity.UserPathHash958C21.initial
#print axioms ShielddSecurity.UserPathHash958C21.initial

set_option pp.all true in
#check @ShielddSecurity.UserPathHash958C21.continuation0_shape
#print axioms ShielddSecurity.UserPathHash958C21.continuation0_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathHash958C21.continuation1_shape
#print axioms ShielddSecurity.UserPathHash958C21.continuation1_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathHash958C21.continuation2_shape
#print axioms ShielddSecurity.UserPathHash958C21.continuation2_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathHash958C21.continuation3_shape
#print axioms ShielddSecurity.UserPathHash958C21.continuation3_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathHash958C21.continuation4_shape
#print axioms ShielddSecurity.UserPathHash958C21.continuation4_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathHash958C21.continuation5_shape
#print axioms ShielddSecurity.UserPathHash958C21.continuation5_shape

set_option pp.all true in
#check @ShielddSecurity.UserPathHash958C21.continuation
#print axioms ShielddSecurity.UserPathHash958C21.continuation

set_option pp.all true in
#check @ShielddSecurity.UserPathHash958C21.hash
#print axioms ShielddSecurity.UserPathHash958C21.hash
