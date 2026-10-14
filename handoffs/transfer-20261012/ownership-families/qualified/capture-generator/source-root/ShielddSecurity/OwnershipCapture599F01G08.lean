-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.OwnershipCapture599F01B64
import ShielddSecurity.OwnershipCapture599F01B65
import ShielddSecurity.OwnershipCapture599F01B66
import ShielddSecurity.OwnershipCapture599F01B67
import ShielddSecurity.OwnershipCapture599F01B68
import ShielddSecurity.OwnershipCapture599F01B69
import ShielddSecurity.OwnershipCapture599F01B70
import ShielddSecurity.OwnershipCapture599F01B71
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipCapture599F01G08
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121570,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121572,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],10084,10854,10640⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := OwnershipCapture599F01B64.entries++OwnershipCapture599F01B65.entries++OwnershipCapture599F01B66.entries++OwnershipCapture599F01B67.entries++OwnershipCapture599F01B68.entries++OwnershipCapture599F01B69.entries++OwnershipCapture599F01B70.entries++OwnershipCapture599F01B71.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : OwnershipCapture599F01B64.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B64.checked
  have h1 : OwnershipCapture599F01B65.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B65.checked
  have h2 : OwnershipCapture599F01B66.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B66.checked
  have h3 : OwnershipCapture599F01B67.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B67.checked
  have h4 : OwnershipCapture599F01B68.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B68.checked
  have h5 : OwnershipCapture599F01B69.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B69.checked
  have h6 : OwnershipCapture599F01B70.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B70.checked
  have h7 : OwnershipCapture599F01B71.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B71.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 65 8 := by
  simp only [entries,List.map_append,OwnershipCapture599F01B64.schedule,OwnershipCapture599F01B65.schedule,OwnershipCapture599F01B66.schedule,OwnershipCapture599F01B67.schedule,OwnershipCapture599F01B68.schedule,OwnershipCapture599F01B69.schedule,OwnershipCapture599F01B70.schedule,OwnershipCapture599F01B71.schedule]
  rfl

end ShielddSecurity.OwnershipCapture599F01G08

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F01G08.checked
#print axioms ShielddSecurity.OwnershipCapture599F01G08.checked

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F01G08.schedule
#print axioms ShielddSecurity.OwnershipCapture599F01G08.schedule
