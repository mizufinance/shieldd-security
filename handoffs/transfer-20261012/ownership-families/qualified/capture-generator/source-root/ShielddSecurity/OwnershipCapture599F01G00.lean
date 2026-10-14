-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.OwnershipCapture599F01B00
import ShielddSecurity.OwnershipCapture599F01B01
import ShielddSecurity.OwnershipCapture599F01B02
import ShielddSecurity.OwnershipCapture599F01B03
import ShielddSecurity.OwnershipCapture599F01B04
import ShielddSecurity.OwnershipCapture599F01B05
import ShielddSecurity.OwnershipCapture599F01B06
import ShielddSecurity.OwnershipCapture599F01B07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipCapture599F01G00
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121570,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121572,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],10084,10854,10640⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := OwnershipCapture599F01B00.entries++OwnershipCapture599F01B01.entries++OwnershipCapture599F01B02.entries++OwnershipCapture599F01B03.entries++OwnershipCapture599F01B04.entries++OwnershipCapture599F01B05.entries++OwnershipCapture599F01B06.entries++OwnershipCapture599F01B07.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : OwnershipCapture599F01B00.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B00.checked
  have h1 : OwnershipCapture599F01B01.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B01.checked
  have h2 : OwnershipCapture599F01B02.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B02.checked
  have h3 : OwnershipCapture599F01B03.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B03.checked
  have h4 : OwnershipCapture599F01B04.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B04.checked
  have h5 : OwnershipCapture599F01B05.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B05.checked
  have h6 : OwnershipCapture599F01B06.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B06.checked
  have h7 : OwnershipCapture599F01B07.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B07.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 1 8 := by
  simp only [entries,List.map_append,OwnershipCapture599F01B00.schedule,OwnershipCapture599F01B01.schedule,OwnershipCapture599F01B02.schedule,OwnershipCapture599F01B03.schedule,OwnershipCapture599F01B04.schedule,OwnershipCapture599F01B05.schedule,OwnershipCapture599F01B06.schedule,OwnershipCapture599F01B07.schedule]
  rfl

end ShielddSecurity.OwnershipCapture599F01G00

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F01G00.checked
#print axioms ShielddSecurity.OwnershipCapture599F01G00.checked

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F01G00.schedule
#print axioms ShielddSecurity.OwnershipCapture599F01G00.schedule
