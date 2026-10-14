-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F01B80
import ShielddSecurity.PayloadCapture558F01B81
import ShielddSecurity.PayloadCapture558F01B82
import ShielddSecurity.PayloadCapture558F01B83
import ShielddSecurity.PayloadCapture558F01B84
import ShielddSecurity.PayloadCapture558F01B85
import ShielddSecurity.PayloadCapture558F01B86
import ShielddSecurity.PayloadCapture558F01B87
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F01G10
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],6335,6840,6698⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F01B80.entries++PayloadCapture558F01B81.entries++PayloadCapture558F01B82.entries++PayloadCapture558F01B83.entries++PayloadCapture558F01B84.entries++PayloadCapture558F01B85.entries++PayloadCapture558F01B86.entries++PayloadCapture558F01B87.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F01B80.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B80.checked
  have h1 : PayloadCapture558F01B81.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B81.checked
  have h2 : PayloadCapture558F01B82.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B82.checked
  have h3 : PayloadCapture558F01B83.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B83.checked
  have h4 : PayloadCapture558F01B84.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B84.checked
  have h5 : PayloadCapture558F01B85.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B85.checked
  have h6 : PayloadCapture558F01B86.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B86.checked
  have h7 : PayloadCapture558F01B87.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B87.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 81 8 := by
  simp only [entries,List.map_append,PayloadCapture558F01B80.schedule,PayloadCapture558F01B81.schedule,PayloadCapture558F01B82.schedule,PayloadCapture558F01B83.schedule,PayloadCapture558F01B84.schedule,PayloadCapture558F01B85.schedule,PayloadCapture558F01B86.schedule,PayloadCapture558F01B87.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F01G10

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F01G10.checked
#print axioms ShielddSecurity.PayloadCapture558F01G10.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F01G10.schedule
#print axioms ShielddSecurity.PayloadCapture558F01G10.schedule
