-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F00B00
import ShielddSecurity.PayloadCapture558F00B01
import ShielddSecurity.PayloadCapture558F00B02
import ShielddSecurity.PayloadCapture558F00B03
import ShielddSecurity.PayloadCapture558F00B04
import ShielddSecurity.PayloadCapture558F00B05
import ShielddSecurity.PayloadCapture558F00B06
import ShielddSecurity.PayloadCapture558F00B07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F00G00
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],4931,5436,5295⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F00B00.entries++PayloadCapture558F00B01.entries++PayloadCapture558F00B02.entries++PayloadCapture558F00B03.entries++PayloadCapture558F00B04.entries++PayloadCapture558F00B05.entries++PayloadCapture558F00B06.entries++PayloadCapture558F00B07.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F00B00.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B00.checked
  have h1 : PayloadCapture558F00B01.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B01.checked
  have h2 : PayloadCapture558F00B02.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B02.checked
  have h3 : PayloadCapture558F00B03.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B03.checked
  have h4 : PayloadCapture558F00B04.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B04.checked
  have h5 : PayloadCapture558F00B05.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B05.checked
  have h6 : PayloadCapture558F00B06.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B06.checked
  have h7 : PayloadCapture558F00B07.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B07.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 1 8 := by
  simp only [entries,List.map_append,PayloadCapture558F00B00.schedule,PayloadCapture558F00B01.schedule,PayloadCapture558F00B02.schedule,PayloadCapture558F00B03.schedule,PayloadCapture558F00B04.schedule,PayloadCapture558F00B05.schedule,PayloadCapture558F00B06.schedule,PayloadCapture558F00B07.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F00G00

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G00.checked
#print axioms ShielddSecurity.PayloadCapture558F00G00.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G00.schedule
#print axioms ShielddSecurity.PayloadCapture558F00G00.schedule
