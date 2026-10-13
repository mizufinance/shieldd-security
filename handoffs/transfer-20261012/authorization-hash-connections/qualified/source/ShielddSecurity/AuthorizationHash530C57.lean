import ShielddSecurity.AuthorizationPermutation529C57B0
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationHash530C57
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def inputs : List Linear := [[(61592,5579934908212736977238010113730457006906792843192217773053283881663622591681),(61596,50978946942794420813356136484142315443152313428221265043903658432145007475423),(61600,51737743277955608982399432577620617083998176562860787771480331520415801857016),(61604,280754542936071555323583947036382301904172335755315562603417507239324752636),(61608,44773762128641970103070913747625047847186741019957383563700055475244115610384),(61612,28552781024861804928696238677004241170376447700649499575281496751792046985224)]]
def result := AuthorizationPermutation529C57B0.result
def parameters := AuthorizationPermutation529C57B0.parameters
variable {F : Type} [Field F] [CharP F p]
def values (rho : Nat → F) := inputs.map (eval rho)
theorem initial (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho (AuthorizationPermutation529C57B0.before i))=
      Poseidon.absorb (Poseidon.initial 18 1) (values rho) := by
  funext i
  have cases : i=⟨0,by decide⟩ ∨ i=⟨1,by decide⟩ ∨ i=⟨2,by decide⟩ := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl <;>
    simp [AuthorizationPermutation529C57B0.before,AuthorizationPoseidonCapture518C57B0R00.before,
      Poseidon.absorb,Poseidon.initial,values,inputs,eval,one,Fin.val_ofNat]
theorem hash (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.hash3 (Poseidon.castParameters parameters) 18 (values rho) := by
  have out := AuthorizationPermutation529C57B0.output rho one linked arithmetic
  rw [initial rho one] at out
  exact out
end ShielddSecurity.AuthorizationHash530C57
set_option pp.all true in
#check @ShielddSecurity.AuthorizationHash530C57.initial
#print axioms ShielddSecurity.AuthorizationHash530C57.initial
set_option pp.all true in
#check @ShielddSecurity.AuthorizationHash530C57.hash
#print axioms ShielddSecurity.AuthorizationHash530C57.hash
