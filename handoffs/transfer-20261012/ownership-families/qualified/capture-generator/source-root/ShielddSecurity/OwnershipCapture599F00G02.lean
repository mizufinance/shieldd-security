-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.OwnershipCapture599F00B16
import ShielddSecurity.OwnershipCapture599F00B17
import ShielddSecurity.OwnershipCapture599F00B18
import ShielddSecurity.OwnershipCapture599F00B19
import ShielddSecurity.OwnershipCapture599F00B20
import ShielddSecurity.OwnershipCapture599F00B21
import ShielddSecurity.OwnershipCapture599F00B22
import ShielddSecurity.OwnershipCapture599F00B23
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipCapture599F00G02
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121570,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121572,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],8552,9322,9100⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := OwnershipCapture599F00B16.entries++OwnershipCapture599F00B17.entries++OwnershipCapture599F00B18.entries++OwnershipCapture599F00B19.entries++OwnershipCapture599F00B20.entries++OwnershipCapture599F00B21.entries++OwnershipCapture599F00B22.entries++OwnershipCapture599F00B23.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : OwnershipCapture599F00B16.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B16.checked
  have h1 : OwnershipCapture599F00B17.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B17.checked
  have h2 : OwnershipCapture599F00B18.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B18.checked
  have h3 : OwnershipCapture599F00B19.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B19.checked
  have h4 : OwnershipCapture599F00B20.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B20.checked
  have h5 : OwnershipCapture599F00B21.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B21.checked
  have h6 : OwnershipCapture599F00B22.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B22.checked
  have h7 : OwnershipCapture599F00B23.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B23.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 17 8 := by
  simp only [entries,List.map_append,OwnershipCapture599F00B16.schedule,OwnershipCapture599F00B17.schedule,OwnershipCapture599F00B18.schedule,OwnershipCapture599F00B19.schedule,OwnershipCapture599F00B20.schedule,OwnershipCapture599F00B21.schedule,OwnershipCapture599F00B22.schedule,OwnershipCapture599F00B23.schedule]
  rfl

end ShielddSecurity.OwnershipCapture599F00G02

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F00G02.checked
#print axioms ShielddSecurity.OwnershipCapture599F00G02.checked

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F00G02.schedule
#print axioms ShielddSecurity.OwnershipCapture599F00G02.schedule
