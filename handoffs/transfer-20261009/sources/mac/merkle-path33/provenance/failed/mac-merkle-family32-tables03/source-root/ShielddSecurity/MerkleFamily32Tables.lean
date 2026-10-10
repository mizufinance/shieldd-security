import ShielddSecurity.MerkleFamily32Audit
import ShielddSecurity.MerkleFamily32Selection
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleFamily32Tables
open Compiler Poseidon CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
def offset (i : Fin 15) := 424*(i.val+2)
def data0 (i : Fin 15) : ReusablePoseidonPhase31.Data 6 :=
  match i.val with
  | 0 => MerkleFamily32L02R0.data
  | 1 => MerkleFamily32L03R0.data
  | 2 => MerkleFamily32L04R0.data
  | 3 => MerkleFamily32L05R0.data
  | 4 => MerkleFamily32L06R0.data
  | 5 => MerkleFamily32L07R0.data
  | 6 => MerkleFamily32L08R0.data
  | 7 => MerkleFamily32L09R0.data
  | 8 => MerkleFamily32L10R0.data
  | 9 => MerkleFamily32L11R0.data
  | 10 => MerkleFamily32L12R0.data
  | 11 => MerkleFamily32L13R0.data
  | 12 => MerkleFamily32L14R0.data
  | 13 => MerkleFamily32L15R0.data
  | 14 => MerkleFamily32L16R0.data
  | _ => MerkleFamily32L02R0.data
theorem certificate0 (i : Fin 15) : ReusablePoseidonPhase31.Certificate (data0 i) := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by have h := i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact MerkleFamily32L02R0.checked
  · exact MerkleFamily32L03R0.checked
  · exact MerkleFamily32L04R0.checked
  · exact MerkleFamily32L05R0.checked
  · exact MerkleFamily32L06R0.checked
  · exact MerkleFamily32L07R0.checked
  · exact MerkleFamily32L08R0.checked
  · exact MerkleFamily32L09R0.checked
  · exact MerkleFamily32L10R0.checked
  · exact MerkleFamily32L11R0.checked
  · exact MerkleFamily32L12R0.checked
  · exact MerkleFamily32L13R0.checked
  · exact MerkleFamily32L14R0.checked
  · exact MerkleFamily32L15R0.checked
  · exact MerkleFamily32L16R0.checked
theorem parameters0 (i : Fin 15) : (data0 i).parameters=TransferPoseidonCall04Shared01.parameters := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by have h := i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
theorem index0 (i : Fin 15) : (data0 i).index=0 := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by have h := i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
theorem bounds0 (i : Fin 15) : (data0 i).low=25048+offset i ∧ (data0 i).high=25064+offset i := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by have h := i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
def data1 (i : Fin 15) : ReusablePoseidonPhase31.Data 6 :=
  match i.val with
  | 0 => MerkleFamily32L02R1.data
  | 1 => MerkleFamily32L03R1.data
  | 2 => MerkleFamily32L04R1.data
  | 3 => MerkleFamily32L05R1.data
  | 4 => MerkleFamily32L06R1.data
  | 5 => MerkleFamily32L07R1.data
  | 6 => MerkleFamily32L08R1.data
  | 7 => MerkleFamily32L09R1.data
  | 8 => MerkleFamily32L10R1.data
  | 9 => MerkleFamily32L11R1.data
  | 10 => MerkleFamily32L12R1.data
  | 11 => MerkleFamily32L13R1.data
  | 12 => MerkleFamily32L14R1.data
  | 13 => MerkleFamily32L15R1.data
  | 14 => MerkleFamily32L16R1.data
  | _ => MerkleFamily32L02R1.data
theorem certificate1 (i : Fin 15) : ReusablePoseidonPhase31.Certificate (data1 i) := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by have h := i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact MerkleFamily32L02R1.checked
  · exact MerkleFamily32L03R1.checked
  · exact MerkleFamily32L04R1.checked
  · exact MerkleFamily32L05R1.checked
  · exact MerkleFamily32L06R1.checked
  · exact MerkleFamily32L07R1.checked
  · exact MerkleFamily32L08R1.checked
  · exact MerkleFamily32L09R1.checked
  · exact MerkleFamily32L10R1.checked
  · exact MerkleFamily32L11R1.checked
  · exact MerkleFamily32L12R1.checked
  · exact MerkleFamily32L13R1.checked
  · exact MerkleFamily32L14R1.checked
  · exact MerkleFamily32L15R1.checked
  · exact MerkleFamily32L16R1.checked
theorem parameters1 (i : Fin 15) : (data1 i).parameters=TransferPoseidonCall04Shared01.parameters := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by have h := i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
theorem index1 (i : Fin 15) : (data1 i).index=1 := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by have h := i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
theorem bounds1 (i : Fin 15) : (data1 i).low=25064+offset i ∧ (data1 i).high=25088+offset i := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by have h := i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
theorem phase_seam (i : Fin 15) : (data1 i).before=(data0 i).after := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by have h := i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
def expectedBefore (i : Fin 15) (k : Fin 6) : Linear :=
  if h0 : k.val=0 then [(0,1282)] else if h1 : k.val=1 then [(0,(i.val+2 : Nat))] else
    MerkleFamily32Selection.outputs i ⟨k.val-2,by omega⟩
def resultList : List Linear := [[(26286,5579934908212736977238010113730457006906792843192217773053283881663622591681),(26290,50978946942794420813356136484142315443152313428221265043903658432145007475423),(26294,51737743277955608982399432577620617083998176562860787771480331520415801857016),(26298,280754542936071555323583947036382301904172335755315562603417507239324752636),(26302,44773762128641970103070913747625047847186741019957383563700055475244115610384),(26306,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(26710,5579934908212736977238010113730457006906792843192217773053283881663622591681),(26714,50978946942794420813356136484142315443152313428221265043903658432145007475423),(26718,51737743277955608982399432577620617083998176562860787771480331520415801857016),(26722,280754542936071555323583947036382301904172335755315562603417507239324752636),(26726,44773762128641970103070913747625047847186741019957383563700055475244115610384),(26730,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(27134,5579934908212736977238010113730457006906792843192217773053283881663622591681),(27138,50978946942794420813356136484142315443152313428221265043903658432145007475423),(27142,51737743277955608982399432577620617083998176562860787771480331520415801857016),(27146,280754542936071555323583947036382301904172335755315562603417507239324752636),(27150,44773762128641970103070913747625047847186741019957383563700055475244115610384),(27154,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(27558,5579934908212736977238010113730457006906792843192217773053283881663622591681),(27562,50978946942794420813356136484142315443152313428221265043903658432145007475423),(27566,51737743277955608982399432577620617083998176562860787771480331520415801857016),(27570,280754542936071555323583947036382301904172335755315562603417507239324752636),(27574,44773762128641970103070913747625047847186741019957383563700055475244115610384),(27578,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(27982,5579934908212736977238010113730457006906792843192217773053283881663622591681),(27986,50978946942794420813356136484142315443152313428221265043903658432145007475423),(27990,51737743277955608982399432577620617083998176562860787771480331520415801857016),(27994,280754542936071555323583947036382301904172335755315562603417507239324752636),(27998,44773762128641970103070913747625047847186741019957383563700055475244115610384),(28002,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(28406,5579934908212736977238010113730457006906792843192217773053283881663622591681),(28410,50978946942794420813356136484142315443152313428221265043903658432145007475423),(28414,51737743277955608982399432577620617083998176562860787771480331520415801857016),(28418,280754542936071555323583947036382301904172335755315562603417507239324752636),(28422,44773762128641970103070913747625047847186741019957383563700055475244115610384),(28426,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(28830,5579934908212736977238010113730457006906792843192217773053283881663622591681),(28834,50978946942794420813356136484142315443152313428221265043903658432145007475423),(28838,51737743277955608982399432577620617083998176562860787771480331520415801857016),(28842,280754542936071555323583947036382301904172335755315562603417507239324752636),(28846,44773762128641970103070913747625047847186741019957383563700055475244115610384),(28850,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(29254,5579934908212736977238010113730457006906792843192217773053283881663622591681),(29258,50978946942794420813356136484142315443152313428221265043903658432145007475423),(29262,51737743277955608982399432577620617083998176562860787771480331520415801857016),(29266,280754542936071555323583947036382301904172335755315562603417507239324752636),(29270,44773762128641970103070913747625047847186741019957383563700055475244115610384),(29274,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(29678,5579934908212736977238010113730457006906792843192217773053283881663622591681),(29682,50978946942794420813356136484142315443152313428221265043903658432145007475423),(29686,51737743277955608982399432577620617083998176562860787771480331520415801857016),(29690,280754542936071555323583947036382301904172335755315562603417507239324752636),(29694,44773762128641970103070913747625047847186741019957383563700055475244115610384),(29698,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(30102,5579934908212736977238010113730457006906792843192217773053283881663622591681),(30106,50978946942794420813356136484142315443152313428221265043903658432145007475423),(30110,51737743277955608982399432577620617083998176562860787771480331520415801857016),(30114,280754542936071555323583947036382301904172335755315562603417507239324752636),(30118,44773762128641970103070913747625047847186741019957383563700055475244115610384),(30122,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(30526,5579934908212736977238010113730457006906792843192217773053283881663622591681),(30530,50978946942794420813356136484142315443152313428221265043903658432145007475423),(30534,51737743277955608982399432577620617083998176562860787771480331520415801857016),(30538,280754542936071555323583947036382301904172335755315562603417507239324752636),(30542,44773762128641970103070913747625047847186741019957383563700055475244115610384),(30546,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(30950,5579934908212736977238010113730457006906792843192217773053283881663622591681),(30954,50978946942794420813356136484142315443152313428221265043903658432145007475423),(30958,51737743277955608982399432577620617083998176562860787771480331520415801857016),(30962,280754542936071555323583947036382301904172335755315562603417507239324752636),(30966,44773762128641970103070913747625047847186741019957383563700055475244115610384),(30970,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(31374,5579934908212736977238010113730457006906792843192217773053283881663622591681),(31378,50978946942794420813356136484142315443152313428221265043903658432145007475423),(31382,51737743277955608982399432577620617083998176562860787771480331520415801857016),(31386,280754542936071555323583947036382301904172335755315562603417507239324752636),(31390,44773762128641970103070913747625047847186741019957383563700055475244115610384),(31394,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(31798,5579934908212736977238010113730457006906792843192217773053283881663622591681),(31802,50978946942794420813356136484142315443152313428221265043903658432145007475423),(31806,51737743277955608982399432577620617083998176562860787771480331520415801857016),(31810,280754542936071555323583947036382301904172335755315562603417507239324752636),(31814,44773762128641970103070913747625047847186741019957383563700055475244115610384),(31818,28552781024861804928696238677004241170376447700649499575281496751792046985224)],[(32222,5579934908212736977238010113730457006906792843192217773053283881663622591681),(32226,50978946942794420813356136484142315443152313428221265043903658432145007475423),(32230,51737743277955608982399432577620617083998176562860787771480331520415801857016),(32234,280754542936071555323583947036382301904172335755315562603417507239324752636),(32238,44773762128641970103070913747625047847186741019957383563700055475244115610384),(32242,28552781024861804928696238677004241170376447700649499575281496751792046985224)]]
def actualResult (i : Fin 15) := resultList[i.val]?.getD []
def previousResult (i : Fin 15) := if i.val=0 then MerkleHash27Whole.actualResult else resultList[i.val-1]?.getD []
def beforeCheck (i : Fin 15) := (List.finRange 6).all (fun k => decide (canonical p ((data0 i).before k)=canonical p (expectedBefore i k)))
def seamCheck (i : Fin 15) := (List.finRange 6).all (fun k => decide (canonical p (ReusableWideTail25.before (offset i) k)=canonical p ((data1 i).after k)))
def resultCheck (i : Fin 15) := decide (canonical p (ReusableWideTail25.after (offset i) 1)=canonical p (actualResult i))
def leafCheck (i : Fin 15) := decide (canonical p (MerkleFamily32Selection.leaf i)=canonical p (previousResult i))
theorem bindings0 : beforeCheck 0=true ∧ seamCheck 0=true ∧ resultCheck 0=true ∧ leafCheck 0=true := by decide +kernel
theorem bindings1 : beforeCheck 1=true ∧ seamCheck 1=true ∧ resultCheck 1=true ∧ leafCheck 1=true := by decide +kernel
theorem bindings2 : beforeCheck 2=true ∧ seamCheck 2=true ∧ resultCheck 2=true ∧ leafCheck 2=true := by decide +kernel
theorem bindings3 : beforeCheck 3=true ∧ seamCheck 3=true ∧ resultCheck 3=true ∧ leafCheck 3=true := by decide +kernel
theorem bindings4 : beforeCheck 4=true ∧ seamCheck 4=true ∧ resultCheck 4=true ∧ leafCheck 4=true := by decide +kernel
theorem bindings5 : beforeCheck 5=true ∧ seamCheck 5=true ∧ resultCheck 5=true ∧ leafCheck 5=true := by decide +kernel
theorem bindings6 : beforeCheck 6=true ∧ seamCheck 6=true ∧ resultCheck 6=true ∧ leafCheck 6=true := by decide +kernel
theorem bindings7 : beforeCheck 7=true ∧ seamCheck 7=true ∧ resultCheck 7=true ∧ leafCheck 7=true := by decide +kernel
theorem bindings8 : beforeCheck 8=true ∧ seamCheck 8=true ∧ resultCheck 8=true ∧ leafCheck 8=true := by decide +kernel
theorem bindings9 : beforeCheck 9=true ∧ seamCheck 9=true ∧ resultCheck 9=true ∧ leafCheck 9=true := by decide +kernel
theorem bindings10 : beforeCheck 10=true ∧ seamCheck 10=true ∧ resultCheck 10=true ∧ leafCheck 10=true := by decide +kernel
theorem bindings11 : beforeCheck 11=true ∧ seamCheck 11=true ∧ resultCheck 11=true ∧ leafCheck 11=true := by decide +kernel
theorem bindings12 : beforeCheck 12=true ∧ seamCheck 12=true ∧ resultCheck 12=true ∧ leafCheck 12=true := by decide +kernel
theorem bindings13 : beforeCheck 13=true ∧ seamCheck 13=true ∧ resultCheck 13=true ∧ leafCheck 13=true := by decide +kernel
theorem bindings14 : beforeCheck 14=true ∧ seamCheck 14=true ∧ resultCheck 14=true ∧ leafCheck 14=true := by decide +kernel
theorem bindings (i : Fin 15) : beforeCheck i=true ∧ seamCheck i=true ∧ resultCheck i=true ∧ leafCheck i=true := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by have h := i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact bindings0
  · exact bindings1
  · exact bindings2
  · exact bindings3
  · exact bindings4
  · exact bindings5
  · exact bindings6
  · exact bindings7
  · exact bindings8
  · exact bindings9
  · exact bindings10
  · exact bindings11
  · exact bindings12
  · exact bindings13
  · exact bindings14
variable {F : Type} [Field F] [CharP F p]
theorem before_values (i : Fin 15) (rho : Nat → F) : (fun k => eval rho ((data0 i).before k))=(fun k => eval rho (expectedBefore i k)) := by
  funext k
  exact canonical_equal (p:=p) rho _ _ (of_decide_eq_true (List.all_eq_true.mp (bindings i).1 k (List.mem_finRange k)))
theorem tail_seam (i : Fin 15) (rho : Nat → F) : (fun k => eval rho (ReusableWideTail25.before (offset i) k))=(fun k => eval rho ((data1 i).after k)) := by
  funext k
  exact canonical_equal (p:=p) rho _ _ (of_decide_eq_true (List.all_eq_true.mp (bindings i).2.1 k (List.mem_finRange k)))
theorem result_values (i : Fin 15) (rho : Nat → F) : eval rho (ReusableWideTail25.after (offset i) 1)=eval rho (actualResult i) :=
  canonical_equal (p:=p) rho _ _ (of_decide_eq_true (bindings i).2.2.1)
theorem leaf_values (i : Fin 15) (rho : Nat → F) : eval rho (MerkleFamily32Selection.leaf i)=eval rho (previousResult i) :=
  canonical_equal (p:=p) rho _ _ (of_decide_eq_true (bindings i).2.2.2)
end ShielddSecurity.MerkleFamily32Tables

set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.offset
#print axioms ShielddSecurity.MerkleFamily32Tables.offset
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.data0
#print axioms ShielddSecurity.MerkleFamily32Tables.data0
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.certificate0
#print axioms ShielddSecurity.MerkleFamily32Tables.certificate0
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.parameters0
#print axioms ShielddSecurity.MerkleFamily32Tables.parameters0
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.index0
#print axioms ShielddSecurity.MerkleFamily32Tables.index0
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bounds0
#print axioms ShielddSecurity.MerkleFamily32Tables.bounds0
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.data1
#print axioms ShielddSecurity.MerkleFamily32Tables.data1
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.certificate1
#print axioms ShielddSecurity.MerkleFamily32Tables.certificate1
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.parameters1
#print axioms ShielddSecurity.MerkleFamily32Tables.parameters1
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.index1
#print axioms ShielddSecurity.MerkleFamily32Tables.index1
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bounds1
#print axioms ShielddSecurity.MerkleFamily32Tables.bounds1
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.phase_seam
#print axioms ShielddSecurity.MerkleFamily32Tables.phase_seam
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.expectedBefore
#print axioms ShielddSecurity.MerkleFamily32Tables.expectedBefore
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.resultList
#print axioms ShielddSecurity.MerkleFamily32Tables.resultList
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.actualResult
#print axioms ShielddSecurity.MerkleFamily32Tables.actualResult
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.previousResult
#print axioms ShielddSecurity.MerkleFamily32Tables.previousResult
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.beforeCheck
#print axioms ShielddSecurity.MerkleFamily32Tables.beforeCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.seamCheck
#print axioms ShielddSecurity.MerkleFamily32Tables.seamCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.resultCheck
#print axioms ShielddSecurity.MerkleFamily32Tables.resultCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.leafCheck
#print axioms ShielddSecurity.MerkleFamily32Tables.leafCheck
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings0
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings0
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings1
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings1
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings2
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings2
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings3
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings3
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings4
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings4
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings5
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings5
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings6
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings6
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings7
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings7
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings8
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings8
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings9
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings9
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings10
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings10
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings11
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings11
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings12
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings12
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings13
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings13
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings14
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings14
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.bindings
#print axioms ShielddSecurity.MerkleFamily32Tables.bindings
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.before_values
#print axioms ShielddSecurity.MerkleFamily32Tables.before_values
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.tail_seam
#print axioms ShielddSecurity.MerkleFamily32Tables.tail_seam
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.result_values
#print axioms ShielddSecurity.MerkleFamily32Tables.result_values
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Tables.leaf_values
#print axioms ShielddSecurity.MerkleFamily32Tables.leaf_values
