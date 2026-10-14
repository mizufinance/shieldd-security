-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.OwnershipCapture599F00B112
import ShielddSecurity.OwnershipCapture599F00B113
import ShielddSecurity.OwnershipCapture599F00B114
import ShielddSecurity.OwnershipCapture599F00B115
import ShielddSecurity.OwnershipCapture599F00B116
import ShielddSecurity.OwnershipCapture599F00B117
import ShielddSecurity.OwnershipCapture599F00B118
import ShielddSecurity.OwnershipCapture599F00B119
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipCapture599F00G14
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121570,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121572,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],8552,9322,9100⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := OwnershipCapture599F00B112.entries++OwnershipCapture599F00B113.entries++OwnershipCapture599F00B114.entries++OwnershipCapture599F00B115.entries++OwnershipCapture599F00B116.entries++OwnershipCapture599F00B117.entries++OwnershipCapture599F00B118.entries++OwnershipCapture599F00B119.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : OwnershipCapture599F00B112.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B112.checked
  have h1 : OwnershipCapture599F00B113.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B113.checked
  have h2 : OwnershipCapture599F00B114.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B114.checked
  have h3 : OwnershipCapture599F00B115.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B115.checked
  have h4 : OwnershipCapture599F00B116.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B116.checked
  have h5 : OwnershipCapture599F00B117.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B117.checked
  have h6 : OwnershipCapture599F00B118.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B118.checked
  have h7 : OwnershipCapture599F00B119.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B119.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 113 8 := by
  simp only [entries,List.map_append,OwnershipCapture599F00B112.schedule,OwnershipCapture599F00B113.schedule,OwnershipCapture599F00B114.schedule,OwnershipCapture599F00B115.schedule,OwnershipCapture599F00B116.schedule,OwnershipCapture599F00B117.schedule,OwnershipCapture599F00B118.schedule,OwnershipCapture599F00B119.schedule]
  rfl

end ShielddSecurity.OwnershipCapture599F00G14

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F00G14.checked
#print axioms ShielddSecurity.OwnershipCapture599F00G14.checked

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F00G14.schedule
#print axioms ShielddSecurity.OwnershipCapture599F00G14.schedule
