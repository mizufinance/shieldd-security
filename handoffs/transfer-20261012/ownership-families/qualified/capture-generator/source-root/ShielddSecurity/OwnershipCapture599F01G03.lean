-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.OwnershipCapture599F01B24
import ShielddSecurity.OwnershipCapture599F01B25
import ShielddSecurity.OwnershipCapture599F01B26
import ShielddSecurity.OwnershipCapture599F01B27
import ShielddSecurity.OwnershipCapture599F01B28
import ShielddSecurity.OwnershipCapture599F01B29
import ShielddSecurity.OwnershipCapture599F01B30
import ShielddSecurity.OwnershipCapture599F01B31
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipCapture599F01G03
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121570,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121572,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],10084,10854,10640⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := OwnershipCapture599F01B24.entries++OwnershipCapture599F01B25.entries++OwnershipCapture599F01B26.entries++OwnershipCapture599F01B27.entries++OwnershipCapture599F01B28.entries++OwnershipCapture599F01B29.entries++OwnershipCapture599F01B30.entries++OwnershipCapture599F01B31.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : OwnershipCapture599F01B24.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B24.checked
  have h1 : OwnershipCapture599F01B25.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B25.checked
  have h2 : OwnershipCapture599F01B26.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B26.checked
  have h3 : OwnershipCapture599F01B27.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B27.checked
  have h4 : OwnershipCapture599F01B28.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B28.checked
  have h5 : OwnershipCapture599F01B29.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B29.checked
  have h6 : OwnershipCapture599F01B30.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B30.checked
  have h7 : OwnershipCapture599F01B31.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B31.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 25 8 := by
  simp only [entries,List.map_append,OwnershipCapture599F01B24.schedule,OwnershipCapture599F01B25.schedule,OwnershipCapture599F01B26.schedule,OwnershipCapture599F01B27.schedule,OwnershipCapture599F01B28.schedule,OwnershipCapture599F01B29.schedule,OwnershipCapture599F01B30.schedule,OwnershipCapture599F01B31.schedule]
  rfl

end ShielddSecurity.OwnershipCapture599F01G03

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F01G03.checked
#print axioms ShielddSecurity.OwnershipCapture599F01G03.checked

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F01G03.schedule
#print axioms ShielddSecurity.OwnershipCapture599F01G03.schedule
