import ShielddSecurity.MerkleFamily32L11R0
import ShielddSecurity.MerkleFamily32L11R1
import ShielddSecurity.MerkleFamily32Selection
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleFamily32BindingL11
open Compiler CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
def expectedBefore (k : Fin 6) : Linear :=
  if h0 : k.val=0 then [(0,1282)] else if h1 : k.val=1 then [(0,11)] else
    MerkleFamily32Selection.outputs 9 ⟨k.val-2,by omega⟩
def actualResult : Linear := [(30102,5579934908212736977238010113730457006906792843192217773053283881663622591681),(30106,50978946942794420813356136484142315443152313428221265043903658432145007475423),(30110,51737743277955608982399432577620617083998176562860787771480331520415801857016),(30114,280754542936071555323583947036382301904172335755315562603417507239324752636),(30118,44773762128641970103070913747625047847186741019957383563700055475244115610384),(30122,28552781024861804928696238677004241170376447700649499575281496751792046985224)]
def previousResult : Linear := [(29678,5579934908212736977238010113730457006906792843192217773053283881663622591681),(29682,50978946942794420813356136484142315443152313428221265043903658432145007475423),(29686,51737743277955608982399432577620617083998176562860787771480331520415801857016),(29690,280754542936071555323583947036382301904172335755315562603417507239324752636),(29694,44773762128641970103070913747625047847186741019957383563700055475244115610384),(29698,28552781024861804928696238677004241170376447700649499575281496751792046985224)]
def beforeCheck := (List.finRange 6).all (fun k => decide (canonical p (MerkleFamily32L11R0.data.before k)=canonical p (expectedBefore k)))
def seamCheck := (List.finRange 6).all (fun k => decide (canonical p (ReusableWideTail25.before 4664 k)=canonical p (MerkleFamily32L11R1.data.after k)))
def resultCheck := decide (canonical p (ReusableWideTail25.after 4664 1)=canonical p actualResult)
def leafCheck := decide (canonical p (MerkleFamily32Selection.leaf 9)=canonical p previousResult)
theorem checked : beforeCheck=true ∧ seamCheck=true ∧ resultCheck=true ∧ leafCheck=true := by decide +kernel
end ShielddSecurity.MerkleFamily32BindingL11

set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL11.expectedBefore
#print axioms ShielddSecurity.MerkleFamily32BindingL11.expectedBefore
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL11.actualResult
#print axioms ShielddSecurity.MerkleFamily32BindingL11.actualResult
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL11.previousResult
#print axioms ShielddSecurity.MerkleFamily32BindingL11.previousResult
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL11.beforeCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL11.beforeCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL11.seamCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL11.seamCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL11.resultCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL11.resultCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL11.leafCheck
#print axioms ShielddSecurity.MerkleFamily32BindingL11.leafCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32BindingL11.checked
#print axioms ShielddSecurity.MerkleFamily32BindingL11.checked
