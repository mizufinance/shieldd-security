-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.OwnershipCapture599F00B72
import ShielddSecurity.OwnershipCapture599F00B73
import ShielddSecurity.OwnershipCapture599F00B74
import ShielddSecurity.OwnershipCapture599F00B75
import ShielddSecurity.OwnershipCapture599F00B76
import ShielddSecurity.OwnershipCapture599F00B77
import ShielddSecurity.OwnershipCapture599F00B78
import ShielddSecurity.OwnershipCapture599F00B79
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipCapture599F00G09
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121570,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121572,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],8552,9322,9100⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := OwnershipCapture599F00B72.entries++OwnershipCapture599F00B73.entries++OwnershipCapture599F00B74.entries++OwnershipCapture599F00B75.entries++OwnershipCapture599F00B76.entries++OwnershipCapture599F00B77.entries++OwnershipCapture599F00B78.entries++OwnershipCapture599F00B79.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : OwnershipCapture599F00B72.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B72.checked
  have h1 : OwnershipCapture599F00B73.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B73.checked
  have h2 : OwnershipCapture599F00B74.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B74.checked
  have h3 : OwnershipCapture599F00B75.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B75.checked
  have h4 : OwnershipCapture599F00B76.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B76.checked
  have h5 : OwnershipCapture599F00B77.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B77.checked
  have h6 : OwnershipCapture599F00B78.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B78.checked
  have h7 : OwnershipCapture599F00B79.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B79.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 73 8 := by
  simp only [entries,List.map_append,OwnershipCapture599F00B72.schedule,OwnershipCapture599F00B73.schedule,OwnershipCapture599F00B74.schedule,OwnershipCapture599F00B75.schedule,OwnershipCapture599F00B76.schedule,OwnershipCapture599F00B77.schedule,OwnershipCapture599F00B78.schedule,OwnershipCapture599F00B79.schedule]
  rfl

end ShielddSecurity.OwnershipCapture599F00G09

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F00G09.checked
#print axioms ShielddSecurity.OwnershipCapture599F00G09.checked

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F00G09.schedule
#print axioms ShielddSecurity.OwnershipCapture599F00G09.schedule
