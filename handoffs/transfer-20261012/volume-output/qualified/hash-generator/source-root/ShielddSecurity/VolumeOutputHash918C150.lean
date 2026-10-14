/- Generated from maintained volume output-hash generator; edit generator or templates. -/
import ShielddSecurity.VolumeOutputHashPermutation917C150
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeOutputHash918C150
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def parameters := VolumeOutputHashPermutation917C150.parameters
noncomputable def result := VolumeOutputHashPermutation917C150.result
noncomputable def inputs : List Linear := [[(1993,1)],[(109304,5579934908212736977238010113730457006906792843192217773053283881663622591681),(109308,50978946942794420813356136484142315443152313428221265043903658432145007475423),(109312,51737743277955608982399432577620617083998176562860787771480331520415801857016),(109316,280754542936071555323583947036382301904172335755315562603417507239324752636),(109320,44773762128641970103070913747625047847186741019957383563700055475244115610384),(109324,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(8387,1)]]
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
theorem initial (rho : Nat → F) (one : rho 0=1) :
    (fun i => eval rho (VolumeOutputHashPermutation917C150.before i))=Poseidon.absorb (Poseidon.initial 7 3) (inputs.map (eval rho)) := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho [(0,775)]=((775:Nat):F)
    norm_num [eval,one]
  · change eval rho [(1993,1)]=0+eval rho [(1993,1)]
    exact (zero_add _).symm
  · change eval rho [(109304,5579934908212736977238010113730457006906792843192217773053283881663622591681),(109308,50978946942794420813356136484142315443152313428221265043903658432145007475423),(109312,51737743277955608982399432577620617083998176562860787771480331520415801857016),(109316,280754542936071555323583947036382301904172335755315562603417507239324752636),(109320,44773762128641970103070913747625047847186741019957383563700055475244115610384),(109324,28552781024861804928696238677004241170376447700649499575281496751792046985224)]=0+eval rho [(109304,5579934908212736977238010113730457006906792843192217773053283881663622591681),(109308,50978946942794420813356136484142315443152313428221265043903658432145007475423),(109312,51737743277955608982399432577620617083998176562860787771480331520415801857016),(109316,280754542936071555323583947036382301904172335755315562603417507239324752636),(109320,44773762128641970103070913747625047847186741019957383563700055475244115610384),(109324,28552781024861804928696238677004241170376447700649499575281496751792046985224)]
    exact (zero_add _).symm
  · change eval rho [(8387,1)]=0+eval rho [(8387,1)]
    exact (zero_add _).symm
  · change (0:F)=0+0
    exact (add_zero _).symm
  · change (0:F)=0+0
    exact (add_zero _).symm
theorem hash (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho result=Poseidon.hash6 (Poseidon.castParameters parameters) 7 (inputs.map (eval rho)) := by
  have permutation := VolumeOutputHashPermutation917C150.permutation rho one linked arithmetic
  rw [initial rho one] at permutation
  have joined := Poseidon.hash6_of_one_block (Poseidon.castParameters parameters) 7 (inputs.map (eval rho))
    (Poseidon.initial 7 3) (fun i => eval rho (VolumeOutputHashPermutation917C150.after i)) rfl rfl permutation
  simpa only [VolumeOutputHashPermutation917C150.result_port,result] using joined
end ShielddSecurity.VolumeOutputHash918C150

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHash918C150.initial
#print axioms ShielddSecurity.VolumeOutputHash918C150.initial

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHash918C150.hash
#print axioms ShielddSecurity.VolumeOutputHash918C150.hash
