-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.OwnershipCapture599F01B40
import ShielddSecurity.OwnershipCapture599F01B41
import ShielddSecurity.OwnershipCapture599F01B42
import ShielddSecurity.OwnershipCapture599F01B43
import ShielddSecurity.OwnershipCapture599F01B44
import ShielddSecurity.OwnershipCapture599F01B45
import ShielddSecurity.OwnershipCapture599F01B46
import ShielddSecurity.OwnershipCapture599F01B47
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipCapture599F01G05
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121570,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121572,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],10084,10854,10640⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := OwnershipCapture599F01B40.entries++OwnershipCapture599F01B41.entries++OwnershipCapture599F01B42.entries++OwnershipCapture599F01B43.entries++OwnershipCapture599F01B44.entries++OwnershipCapture599F01B45.entries++OwnershipCapture599F01B46.entries++OwnershipCapture599F01B47.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : OwnershipCapture599F01B40.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B40.checked
  have h1 : OwnershipCapture599F01B41.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B41.checked
  have h2 : OwnershipCapture599F01B42.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B42.checked
  have h3 : OwnershipCapture599F01B43.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B43.checked
  have h4 : OwnershipCapture599F01B44.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B44.checked
  have h5 : OwnershipCapture599F01B45.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B45.checked
  have h6 : OwnershipCapture599F01B46.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B46.checked
  have h7 : OwnershipCapture599F01B47.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B47.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 41 8 := by
  simp only [entries,List.map_append,OwnershipCapture599F01B40.schedule,OwnershipCapture599F01B41.schedule,OwnershipCapture599F01B42.schedule,OwnershipCapture599F01B43.schedule,OwnershipCapture599F01B44.schedule,OwnershipCapture599F01B45.schedule,OwnershipCapture599F01B46.schedule,OwnershipCapture599F01B47.schedule]
  rfl

end ShielddSecurity.OwnershipCapture599F01G05

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F01G05.checked
#print axioms ShielddSecurity.OwnershipCapture599F01G05.checked

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F01G05.schedule
#print axioms ShielddSecurity.OwnershipCapture599F01G05.schedule
