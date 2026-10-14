-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.OwnershipCapture599F00B104
import ShielddSecurity.OwnershipCapture599F00B105
import ShielddSecurity.OwnershipCapture599F00B106
import ShielddSecurity.OwnershipCapture599F00B107
import ShielddSecurity.OwnershipCapture599F00B108
import ShielddSecurity.OwnershipCapture599F00B109
import ShielddSecurity.OwnershipCapture599F00B110
import ShielddSecurity.OwnershipCapture599F00B111
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipCapture599F00G13
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121570,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121572,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],8552,9322,9100⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := OwnershipCapture599F00B104.entries++OwnershipCapture599F00B105.entries++OwnershipCapture599F00B106.entries++OwnershipCapture599F00B107.entries++OwnershipCapture599F00B108.entries++OwnershipCapture599F00B109.entries++OwnershipCapture599F00B110.entries++OwnershipCapture599F00B111.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : OwnershipCapture599F00B104.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B104.checked
  have h1 : OwnershipCapture599F00B105.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B105.checked
  have h2 : OwnershipCapture599F00B106.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B106.checked
  have h3 : OwnershipCapture599F00B107.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B107.checked
  have h4 : OwnershipCapture599F00B108.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B108.checked
  have h5 : OwnershipCapture599F00B109.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B109.checked
  have h6 : OwnershipCapture599F00B110.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B110.checked
  have h7 : OwnershipCapture599F00B111.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F00B111.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 105 8 := by
  simp only [entries,List.map_append,OwnershipCapture599F00B104.schedule,OwnershipCapture599F00B105.schedule,OwnershipCapture599F00B106.schedule,OwnershipCapture599F00B107.schedule,OwnershipCapture599F00B108.schedule,OwnershipCapture599F00B109.schedule,OwnershipCapture599F00B110.schedule,OwnershipCapture599F00B111.schedule]
  rfl

end ShielddSecurity.OwnershipCapture599F00G13

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F00G13.checked
#print axioms ShielddSecurity.OwnershipCapture599F00G13.checked

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F00G13.schedule
#print axioms ShielddSecurity.OwnershipCapture599F00G13.schedule
