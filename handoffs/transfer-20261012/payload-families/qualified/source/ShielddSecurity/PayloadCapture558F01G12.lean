-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F01B96
import ShielddSecurity.PayloadCapture558F01B97
import ShielddSecurity.PayloadCapture558F01B98
import ShielddSecurity.PayloadCapture558F01B99
import ShielddSecurity.PayloadCapture558F01B100
import ShielddSecurity.PayloadCapture558F01B101
import ShielddSecurity.PayloadCapture558F01B102
import ShielddSecurity.PayloadCapture558F01B103
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F01G12
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],6335,6840,6698⟩
def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F01B96.entries++PayloadCapture558F01B97.entries++PayloadCapture558F01B98.entries++PayloadCapture558F01B99.entries++PayloadCapture558F01B100.entries++PayloadCapture558F01B101.entries++PayloadCapture558F01B102.entries++PayloadCapture558F01B103.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F01B96.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B96.checked
  have h1 : PayloadCapture558F01B97.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B97.checked
  have h2 : PayloadCapture558F01B98.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B98.checked
  have h3 : PayloadCapture558F01B99.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B99.checked
  have h4 : PayloadCapture558F01B100.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B100.checked
  have h5 : PayloadCapture558F01B101.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B101.checked
  have h6 : PayloadCapture558F01B102.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B102.checked
  have h7 : PayloadCapture558F01B103.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B103.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 97 8 := by
  simp only [entries,List.map_append,PayloadCapture558F01B96.schedule,PayloadCapture558F01B97.schedule,PayloadCapture558F01B98.schedule,PayloadCapture558F01B99.schedule,PayloadCapture558F01B100.schedule,PayloadCapture558F01B101.schedule,PayloadCapture558F01B102.schedule,PayloadCapture558F01B103.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F01G12

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F01G12.checked
#print axioms ShielddSecurity.PayloadCapture558F01G12.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F01G12.schedule
#print axioms ShielddSecurity.PayloadCapture558F01G12.schedule
