import ShielddSecurity.MerkleFamily32L12R0
import ShielddSecurity.MerkleFamily32L12R1
import ShielddSecurity.MerkleFamily32Selection
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleFamily32BindingL12
open Compiler CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
def expectedBefore (k : Fin 6) : Linear :=
  if h0 : k.val=0 then [(0,1282)] else if h1 : k.val=1 then [(0,12)] else
    MerkleFamily32Selection.outputs 10 ⟨k.val-2,by omega⟩
def actualResult : Linear := [(30526,5579934908212736977238010113730457006906792843192217773053283881663622591681),(30530,50978946942794420813356136484142315443152313428221265043903658432145007475423),(30534,51737743277955608982399432577620617083998176562860787771480331520415801857016),(30538,280754542936071555323583947036382301904172335755315562603417507239324752636),(30542,44773762128641970103070913747625047847186741019957383563700055475244115610384),(30546,28552781024861804928696238677004241170376447700649499575281496751792046985224)]
def previousResult : Linear := [(30102,5579934908212736977238010113730457006906792843192217773053283881663622591681),(30106,50978946942794420813356136484142315443152313428221265043903658432145007475423),(30110,51737743277955608982399432577620617083998176562860787771480331520415801857016),(30114,280754542936071555323583947036382301904172335755315562603417507239324752636),(30118,44773762128641970103070913747625047847186741019957383563700055475244115610384),(30122,28552781024861804928696238677004241170376447700649499575281496751792046985224)]
def beforeCheck := (List.finRange 6).all (fun k => decide (canonical p (MerkleFamily32L12R0.data.before k)=canonical p (expectedBefore k)))
def seamCheck := (List.finRange 6).all (fun k => decide (canonical p (ReusableWideTail25.before 5088 k)=canonical p (MerkleFamily32L12R1.data.after k)))
def resultCheck := decide (canonical p (ReusableWideTail25.after 5088 1)=canonical p actualResult)
def leafCheck := decide (canonical p (MerkleFamily32Selection.leaf 10)=canonical p previousResult)
theorem checked : beforeCheck=true ∧ seamCheck=true ∧ resultCheck=true ∧ leafCheck=true := by decide +kernel
end ShielddSecurity.MerkleFamily32BindingL12

set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL12.expectedBefore
#print axioms ShielddSecurity.MerkleFamily32BindingL12.expectedBefore
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL12.actualResult
#print axioms ShielddSecurity.MerkleFamily32BindingL12.actualResult
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL12.previousResult
#print axioms ShielddSecurity.MerkleFamily32BindingL12.previousResult
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL12.beforeCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL12.beforeCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL12.seamCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL12.seamCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL12.resultCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL12.resultCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL12.leafCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL12.leafCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL12.checked
#print axioms ShielddSecurity.MerkleFamily32BindingL12.checked
