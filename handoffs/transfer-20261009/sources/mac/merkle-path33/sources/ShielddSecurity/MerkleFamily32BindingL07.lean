import ShielddSecurity.MerkleFamily32L07R0
import ShielddSecurity.MerkleFamily32L07R1
import ShielddSecurity.MerkleFamily32Selection
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleFamily32BindingL07
open Compiler CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
def expectedBefore (k : Fin 6) : Linear :=
  if h0 : k.val=0 then [(0,1282)] else if h1 : k.val=1 then [(0,7)] else
    MerkleFamily32Selection.outputs 5 ⟨k.val-2,by omega⟩
def actualResult : Linear := [(28406,5579934908212736977238010113730457006906792843192217773053283881663622591681),(28410,50978946942794420813356136484142315443152313428221265043903658432145007475423),(28414,51737743277955608982399432577620617083998176562860787771480331520415801857016),(28418,280754542936071555323583947036382301904172335755315562603417507239324752636),(28422,44773762128641970103070913747625047847186741019957383563700055475244115610384),(28426,28552781024861804928696238677004241170376447700649499575281496751792046985224)]
def previousResult : Linear := [(27982,5579934908212736977238010113730457006906792843192217773053283881663622591681),(27986,50978946942794420813356136484142315443152313428221265043903658432145007475423),(27990,51737743277955608982399432577620617083998176562860787771480331520415801857016),(27994,280754542936071555323583947036382301904172335755315562603417507239324752636),(27998,44773762128641970103070913747625047847186741019957383563700055475244115610384),(28002,28552781024861804928696238677004241170376447700649499575281496751792046985224)]
def beforeCheck := (List.finRange 6).all (fun k => decide (canonical p (MerkleFamily32L07R0.data.before k)=canonical p (expectedBefore k)))
def seamCheck := (List.finRange 6).all (fun k => decide (canonical p (ReusableWideTail25.before 2968 k)=canonical p (MerkleFamily32L07R1.data.after k)))
def resultCheck := decide (canonical p (ReusableWideTail25.after 2968 1)=canonical p actualResult)
def leafCheck := decide (canonical p (MerkleFamily32Selection.leaf 5)=canonical p previousResult)
theorem checked : beforeCheck=true ∧ seamCheck=true ∧ resultCheck=true ∧ leafCheck=true := by decide +kernel
end ShielddSecurity.MerkleFamily32BindingL07

set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL07.expectedBefore
#print axioms ShielddSecurity.MerkleFamily32BindingL07.expectedBefore
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL07.actualResult
#print axioms ShielddSecurity.MerkleFamily32BindingL07.actualResult
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL07.previousResult
#print axioms ShielddSecurity.MerkleFamily32BindingL07.previousResult
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL07.beforeCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL07.beforeCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL07.seamCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL07.seamCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL07.resultCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL07.resultCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL07.leafCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL07.leafCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL07.checked
#print axioms ShielddSecurity.MerkleFamily32BindingL07.checked
