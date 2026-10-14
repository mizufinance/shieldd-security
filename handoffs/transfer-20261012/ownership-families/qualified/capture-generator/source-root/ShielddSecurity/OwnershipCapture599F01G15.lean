-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.OwnershipCapture599F01B120
import ShielddSecurity.OwnershipCapture599F01B121
import ShielddSecurity.OwnershipCapture599F01B122
import ShielddSecurity.OwnershipCapture599F01B123
import ShielddSecurity.OwnershipCapture599F01B124
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipCapture599F01G15
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121570,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121572,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],10084,10854,10640⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := OwnershipCapture599F01B120.entries++OwnershipCapture599F01B121.entries++OwnershipCapture599F01B122.entries++OwnershipCapture599F01B123.entries++OwnershipCapture599F01B124.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : OwnershipCapture599F01B120.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B120.checked
  have h1 : OwnershipCapture599F01B121.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B121.checked
  have h2 : OwnershipCapture599F01B122.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B122.checked
  have h3 : OwnershipCapture599F01B123.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B123.checked
  have h4 : OwnershipCapture599F01B124.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01B124.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 121 5 := by
  simp only [entries,List.map_append,OwnershipCapture599F01B120.schedule,OwnershipCapture599F01B121.schedule,OwnershipCapture599F01B122.schedule,OwnershipCapture599F01B123.schedule,OwnershipCapture599F01B124.schedule]
  rfl

end ShielddSecurity.OwnershipCapture599F01G15

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F01G15.checked
#print axioms ShielddSecurity.OwnershipCapture599F01G15.checked

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F01G15.schedule
#print axioms ShielddSecurity.OwnershipCapture599F01G15.schedule
