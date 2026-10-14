-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F00B24
import ShielddSecurity.PayloadCapture558F00B25
import ShielddSecurity.PayloadCapture558F00B26
import ShielddSecurity.PayloadCapture558F00B27
import ShielddSecurity.PayloadCapture558F00B28
import ShielddSecurity.PayloadCapture558F00B29
import ShielddSecurity.PayloadCapture558F00B30
import ShielddSecurity.PayloadCapture558F00B31
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F00G03
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],4931,5436,5295⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F00B24.entries++PayloadCapture558F00B25.entries++PayloadCapture558F00B26.entries++PayloadCapture558F00B27.entries++PayloadCapture558F00B28.entries++PayloadCapture558F00B29.entries++PayloadCapture558F00B30.entries++PayloadCapture558F00B31.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F00B24.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B24.checked
  have h1 : PayloadCapture558F00B25.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B25.checked
  have h2 : PayloadCapture558F00B26.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B26.checked
  have h3 : PayloadCapture558F00B27.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B27.checked
  have h4 : PayloadCapture558F00B28.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B28.checked
  have h5 : PayloadCapture558F00B29.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B29.checked
  have h6 : PayloadCapture558F00B30.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B30.checked
  have h7 : PayloadCapture558F00B31.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B31.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 25 8 := by
  simp only [entries,List.map_append,PayloadCapture558F00B24.schedule,PayloadCapture558F00B25.schedule,PayloadCapture558F00B26.schedule,PayloadCapture558F00B27.schedule,PayloadCapture558F00B28.schedule,PayloadCapture558F00B29.schedule,PayloadCapture558F00B30.schedule,PayloadCapture558F00B31.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F00G03

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G03.checked
#print axioms ShielddSecurity.PayloadCapture558F00G03.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G03.schedule
#print axioms ShielddSecurity.PayloadCapture558F00G03.schedule
