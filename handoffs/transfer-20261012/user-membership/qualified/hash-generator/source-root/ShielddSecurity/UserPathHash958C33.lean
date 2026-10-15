/- Generated from maintained user path-hash generator; edit generator or templates. -/
import ShielddSecurity.UserPathHashPermutation957C33B0
import ShielddSecurity.WideHashTwoBlocks960
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathHash958C33
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def parameters := UserPathHashPermutation957C33B0.parameters
noncomputable def result := UserPathHashPermutation957C33B0.result
noncomputable def inputs : List Linear := [[(0,12)],[(39484,5579934908212736977238010113730457006906792843192217773053283881663622591681),(39488,50978946942794420813356136484142315443152313428221265043903658432145007475423),(39492,51737743277955608982399432577620617083998176562860787771480331520415801857016),(39496,280754542936071555323583947036382301904172335755315562603417507239324752636),(39500,44773762128641970103070913747625047847186741019957383563700055475244115610384),(39504,28552781024861804928696238677004241170376447700649499575281496751792046985224),(39506,1),(39510,1)],[(1564,1),(39506,52435875175126190479447740508185965837690552500527637822603658699938581184512),(39512,1)],[(1565,1),(39514,1)],[(1566,1),(39516,1)]]
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
theorem initial (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho (UserPathHashPermutation957C33B0.before i))=Poseidon.absorb (Poseidon.initial 3 5) (inputs.map (eval rho)) := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho [(0,1283)]=((1283:Nat):F)
    norm_num [eval,one]
  · change eval rho [(0,12)]=0+eval rho [(0,12)]
    exact (zero_add _).symm
  · change eval rho [(39484,5579934908212736977238010113730457006906792843192217773053283881663622591681),(39488,50978946942794420813356136484142315443152313428221265043903658432145007475423),(39492,51737743277955608982399432577620617083998176562860787771480331520415801857016),(39496,280754542936071555323583947036382301904172335755315562603417507239324752636),(39500,44773762128641970103070913747625047847186741019957383563700055475244115610384),(39504,28552781024861804928696238677004241170376447700649499575281496751792046985224),(39506,1),(39510,1)]=0+eval rho [(39484,5579934908212736977238010113730457006906792843192217773053283881663622591681),(39488,50978946942794420813356136484142315443152313428221265043903658432145007475423),(39492,51737743277955608982399432577620617083998176562860787771480331520415801857016),(39496,280754542936071555323583947036382301904172335755315562603417507239324752636),(39500,44773762128641970103070913747625047847186741019957383563700055475244115610384),(39504,28552781024861804928696238677004241170376447700649499575281496751792046985224),(39506,1),(39510,1)]
    exact (zero_add _).symm
  · change eval rho [(1564,1),(39506,52435875175126190479447740508185965837690552500527637822603658699938581184512),(39512,1)]=0+eval rho [(1564,1),(39506,52435875175126190479447740508185965837690552500527637822603658699938581184512),(39512,1)]
    exact (zero_add _).symm
  · change eval rho [(1565,1),(39514,1)]=0+eval rho [(1565,1),(39514,1)]
    exact (zero_add _).symm
  · change eval rho [(1566,1),(39516,1)]=0+eval rho [(1566,1),(39516,1)]
    exact (zero_add _).symm
theorem hash (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.hash6 (Poseidon.castParameters parameters) 3 (inputs.map (eval rho)) := by
  have first := UserPathHashPermutation957C33B0.permutation rho one linked arithmetic
  rw [initial rho one] at first
  have joined := Poseidon.hash6_of_one_block (Poseidon.castParameters parameters) 3 (inputs.map (eval rho))
    (Poseidon.initial 3 5) (fun i => eval rho (UserPathHashPermutation957C33B0.after i)) rfl rfl first
  simpa only [UserPathHashPermutation957C33B0.result_port,result] using joined
end ShielddSecurity.UserPathHash958C33

set_option pp.all true in
#check @ShielddSecurity.UserPathHash958C33.initial
#print axioms ShielddSecurity.UserPathHash958C33.initial

set_option pp.all true in
#check @ShielddSecurity.UserPathHash958C33.hash
#print axioms ShielddSecurity.UserPathHash958C33.hash
