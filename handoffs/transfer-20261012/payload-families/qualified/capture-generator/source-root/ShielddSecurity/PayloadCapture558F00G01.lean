-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F00B08
import ShielddSecurity.PayloadCapture558F00B09
import ShielddSecurity.PayloadCapture558F00B10
import ShielddSecurity.PayloadCapture558F00B11
import ShielddSecurity.PayloadCapture558F00B12
import ShielddSecurity.PayloadCapture558F00B13
import ShielddSecurity.PayloadCapture558F00B14
import ShielddSecurity.PayloadCapture558F00B15
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F00G01
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],4931,5436,5295⟩
def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F00B08.entries++PayloadCapture558F00B09.entries++PayloadCapture558F00B10.entries++PayloadCapture558F00B11.entries++PayloadCapture558F00B12.entries++PayloadCapture558F00B13.entries++PayloadCapture558F00B14.entries++PayloadCapture558F00B15.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F00B08.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B08.checked
  have h1 : PayloadCapture558F00B09.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B09.checked
  have h2 : PayloadCapture558F00B10.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B10.checked
  have h3 : PayloadCapture558F00B11.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B11.checked
  have h4 : PayloadCapture558F00B12.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B12.checked
  have h5 : PayloadCapture558F00B13.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B13.checked
  have h6 : PayloadCapture558F00B14.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B14.checked
  have h7 : PayloadCapture558F00B15.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00B15.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 9 8 := by
  simp only [entries,List.map_append,PayloadCapture558F00B08.schedule,PayloadCapture558F00B09.schedule,PayloadCapture558F00B10.schedule,PayloadCapture558F00B11.schedule,PayloadCapture558F00B12.schedule,PayloadCapture558F00B13.schedule,PayloadCapture558F00B14.schedule,PayloadCapture558F00B15.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F00G01

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G01.checked
#print axioms ShielddSecurity.PayloadCapture558F00G01.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00G01.schedule
#print axioms ShielddSecurity.PayloadCapture558F00G01.schedule
