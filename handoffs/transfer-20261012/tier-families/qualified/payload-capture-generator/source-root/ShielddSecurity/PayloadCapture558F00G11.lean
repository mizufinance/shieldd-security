-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F00B88
import ShielddSecurity.PayloadCapture558F00B89
import ShielddSecurity.PayloadCapture558F00B90
import ShielddSecurity.PayloadCapture558F00B91
import ShielddSecurity.PayloadCapture558F00B92
import ShielddSecurity.PayloadCapture558F00B93
import ShielddSecurity.PayloadCapture558F00B94
import ShielddSecurity.PayloadCapture558F00B95
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F00G11
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],4931,5436,5295⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F00B88.entries++PayloadCapture558F00B89.entries++PayloadCapture558F00B90.entries++PayloadCapture558F00B91.entries++PayloadCapture558F00B92.entries++PayloadCapture558F00B93.entries++PayloadCapture558F00B94.entries++PayloadCapture558F00B95.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F00B88.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B88.checked
  have h1 : PayloadCapture558F00B89.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B89.checked
  have h2 : PayloadCapture558F00B90.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B90.checked
  have h3 : PayloadCapture558F00B91.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B91.checked
  have h4 : PayloadCapture558F00B92.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B92.checked
  have h5 : PayloadCapture558F00B93.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B93.checked
  have h6 : PayloadCapture558F00B94.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B94.checked
  have h7 : PayloadCapture558F00B95.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B95.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 89 8 := by
  simp only [entries,List.map_append,PayloadCapture558F00B88.schedule,PayloadCapture558F00B89.schedule,PayloadCapture558F00B90.schedule,PayloadCapture558F00B91.schedule,PayloadCapture558F00B92.schedule,PayloadCapture558F00B93.schedule,PayloadCapture558F00B94.schedule,PayloadCapture558F00B95.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F00G11

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G11.checked
#print axioms ShielddSecurity.PayloadCapture558F00G11.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G11.schedule
#print axioms ShielddSecurity.PayloadCapture558F00G11.schedule
