import ShielddSecurity.MerkleFamily32L14R0
import ShielddSecurity.MerkleFamily32L14R1
import ShielddSecurity.MerkleFamily32Selection
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleFamily32BindingL14
open Compiler CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
def expectedBefore (k : Fin 6) : Linear :=
  if h0 : k.val=0 then [(0,1282)] else if h1 : k.val=1 then [(0,14)] else
    MerkleFamily32Selection.outputs 12 ⟨k.val-2,by omega⟩
def actualResult : Linear := [(31374,5579934908212736977238010113730457006906792843192217773053283881663622591681),(31378,50978946942794420813356136484142315443152313428221265043903658432145007475423),(31382,51737743277955608982399432577620617083998176562860787771480331520415801857016),(31386,280754542936071555323583947036382301904172335755315562603417507239324752636),(31390,44773762128641970103070913747625047847186741019957383563700055475244115610384),(31394,28552781024861804928696238677004241170376447700649499575281496751792046985224)]
def previousResult : Linear := [(30950,5579934908212736977238010113730457006906792843192217773053283881663622591681),(30954,50978946942794420813356136484142315443152313428221265043903658432145007475423),(30958,51737743277955608982399432577620617083998176562860787771480331520415801857016),(30962,280754542936071555323583947036382301904172335755315562603417507239324752636),(30966,44773762128641970103070913747625047847186741019957383563700055475244115610384),(30970,28552781024861804928696238677004241170376447700649499575281496751792046985224)]
def beforeCheck := (List.finRange 6).all (fun k => decide (canonical p (MerkleFamily32L14R0.data.before k)=canonical p (expectedBefore k)))
def seamCheck := (List.finRange 6).all (fun k => decide (canonical p (ReusableWideTail25.before 5936 k)=canonical p (MerkleFamily32L14R1.data.after k)))
def resultCheck := decide (canonical p (ReusableWideTail25.after 5936 1)=canonical p actualResult)
def leafCheck := decide (canonical p (MerkleFamily32Selection.leaf 12)=canonical p previousResult)
theorem checked : beforeCheck=true ∧ seamCheck=true ∧ resultCheck=true ∧ leafCheck=true := by decide +kernel
end ShielddSecurity.MerkleFamily32BindingL14

set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL14.expectedBefore
#print axioms ShielddSecurity.MerkleFamily32BindingL14.expectedBefore
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL14.actualResult
#print axioms ShielddSecurity.MerkleFamily32BindingL14.actualResult
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL14.previousResult
#print axioms ShielddSecurity.MerkleFamily32BindingL14.previousResult
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL14.beforeCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL14.beforeCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL14.seamCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL14.seamCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL14.resultCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL14.resultCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL14.leafCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL14.leafCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL14.checked
#print axioms ShielddSecurity.MerkleFamily32BindingL14.checked
