-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F00B72
import ShielddSecurity.PayloadCapture558F00B73
import ShielddSecurity.PayloadCapture558F00B74
import ShielddSecurity.PayloadCapture558F00B75
import ShielddSecurity.PayloadCapture558F00B76
import ShielddSecurity.PayloadCapture558F00B77
import ShielddSecurity.PayloadCapture558F00B78
import ShielddSecurity.PayloadCapture558F00B79
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F00G09
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],4931,5436,5295⟩
def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F00B72.entries++PayloadCapture558F00B73.entries++PayloadCapture558F00B74.entries++PayloadCapture558F00B75.entries++PayloadCapture558F00B76.entries++PayloadCapture558F00B77.entries++PayloadCapture558F00B78.entries++PayloadCapture558F00B79.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F00B72.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B72.checked
  have h1 : PayloadCapture558F00B73.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B73.checked
  have h2 : PayloadCapture558F00B74.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B74.checked
  have h3 : PayloadCapture558F00B75.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B75.checked
  have h4 : PayloadCapture558F00B76.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B76.checked
  have h5 : PayloadCapture558F00B77.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B77.checked
  have h6 : PayloadCapture558F00B78.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B78.checked
  have h7 : PayloadCapture558F00B79.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B79.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 73 8 := by
  simp only [entries,List.map_append,PayloadCapture558F00B72.schedule,PayloadCapture558F00B73.schedule,PayloadCapture558F00B74.schedule,PayloadCapture558F00B75.schedule,PayloadCapture558F00B76.schedule,PayloadCapture558F00B77.schedule,PayloadCapture558F00B78.schedule,PayloadCapture558F00B79.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F00G09

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G09.checked
#print axioms ShielddSecurity.PayloadCapture558F00G09.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G09.schedule
#print axioms ShielddSecurity.PayloadCapture558F00G09.schedule
