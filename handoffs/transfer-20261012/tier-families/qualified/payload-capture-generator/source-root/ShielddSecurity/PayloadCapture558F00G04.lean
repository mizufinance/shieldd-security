-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F00B32
import ShielddSecurity.PayloadCapture558F00B33
import ShielddSecurity.PayloadCapture558F00B34
import ShielddSecurity.PayloadCapture558F00B35
import ShielddSecurity.PayloadCapture558F00B36
import ShielddSecurity.PayloadCapture558F00B37
import ShielddSecurity.PayloadCapture558F00B38
import ShielddSecurity.PayloadCapture558F00B39
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F00G04
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],4931,5436,5295⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F00B32.entries++PayloadCapture558F00B33.entries++PayloadCapture558F00B34.entries++PayloadCapture558F00B35.entries++PayloadCapture558F00B36.entries++PayloadCapture558F00B37.entries++PayloadCapture558F00B38.entries++PayloadCapture558F00B39.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F00B32.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B32.checked
  have h1 : PayloadCapture558F00B33.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B33.checked
  have h2 : PayloadCapture558F00B34.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B34.checked
  have h3 : PayloadCapture558F00B35.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B35.checked
  have h4 : PayloadCapture558F00B36.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B36.checked
  have h5 : PayloadCapture558F00B37.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B37.checked
  have h6 : PayloadCapture558F00B38.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B38.checked
  have h7 : PayloadCapture558F00B39.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B39.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 33 8 := by
  simp only [entries,List.map_append,PayloadCapture558F00B32.schedule,PayloadCapture558F00B33.schedule,PayloadCapture558F00B34.schedule,PayloadCapture558F00B35.schedule,PayloadCapture558F00B36.schedule,PayloadCapture558F00B37.schedule,PayloadCapture558F00B38.schedule,PayloadCapture558F00B39.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F00G04

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G04.checked
#print axioms ShielddSecurity.PayloadCapture558F00G04.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G04.schedule
#print axioms ShielddSecurity.PayloadCapture558F00G04.schedule
