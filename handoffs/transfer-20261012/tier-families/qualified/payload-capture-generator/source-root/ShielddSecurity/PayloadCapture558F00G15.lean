-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F00B120
import ShielddSecurity.PayloadCapture558F00B121
import ShielddSecurity.PayloadCapture558F00B122
import ShielddSecurity.PayloadCapture558F00B123
import ShielddSecurity.PayloadCapture558F00B124
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F00G15
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],4931,5436,5295⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F00B120.entries++PayloadCapture558F00B121.entries++PayloadCapture558F00B122.entries++PayloadCapture558F00B123.entries++PayloadCapture558F00B124.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F00B120.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B120.checked
  have h1 : PayloadCapture558F00B121.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B121.checked
  have h2 : PayloadCapture558F00B122.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B122.checked
  have h3 : PayloadCapture558F00B123.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B123.checked
  have h4 : PayloadCapture558F00B124.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B124.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 121 5 := by
  simp only [entries,List.map_append,PayloadCapture558F00B120.schedule,PayloadCapture558F00B121.schedule,PayloadCapture558F00B122.schedule,PayloadCapture558F00B123.schedule,PayloadCapture558F00B124.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F00G15

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G15.checked
#print axioms ShielddSecurity.PayloadCapture558F00G15.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G15.schedule
#print axioms ShielddSecurity.PayloadCapture558F00G15.schedule
