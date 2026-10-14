-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F01B48
import ShielddSecurity.PayloadCapture558F01B49
import ShielddSecurity.PayloadCapture558F01B50
import ShielddSecurity.PayloadCapture558F01B51
import ShielddSecurity.PayloadCapture558F01B52
import ShielddSecurity.PayloadCapture558F01B53
import ShielddSecurity.PayloadCapture558F01B54
import ShielddSecurity.PayloadCapture558F01B55
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F01G06
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],6335,6840,6698⟩
def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F01B48.entries++PayloadCapture558F01B49.entries++PayloadCapture558F01B50.entries++PayloadCapture558F01B51.entries++PayloadCapture558F01B52.entries++PayloadCapture558F01B53.entries++PayloadCapture558F01B54.entries++PayloadCapture558F01B55.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F01B48.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B48.checked
  have h1 : PayloadCapture558F01B49.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B49.checked
  have h2 : PayloadCapture558F01B50.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B50.checked
  have h3 : PayloadCapture558F01B51.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B51.checked
  have h4 : PayloadCapture558F01B52.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B52.checked
  have h5 : PayloadCapture558F01B53.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B53.checked
  have h6 : PayloadCapture558F01B54.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B54.checked
  have h7 : PayloadCapture558F01B55.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B55.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 49 8 := by
  simp only [entries,List.map_append,PayloadCapture558F01B48.schedule,PayloadCapture558F01B49.schedule,PayloadCapture558F01B50.schedule,PayloadCapture558F01B51.schedule,PayloadCapture558F01B52.schedule,PayloadCapture558F01B53.schedule,PayloadCapture558F01B54.schedule,PayloadCapture558F01B55.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F01G06

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F01G06.checked
#print axioms ShielddSecurity.PayloadCapture558F01G06.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F01G06.schedule
#print axioms ShielddSecurity.PayloadCapture558F01G06.schedule
