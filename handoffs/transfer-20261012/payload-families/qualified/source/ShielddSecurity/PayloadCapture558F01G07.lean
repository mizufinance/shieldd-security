-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F01B56
import ShielddSecurity.PayloadCapture558F01B57
import ShielddSecurity.PayloadCapture558F01B58
import ShielddSecurity.PayloadCapture558F01B59
import ShielddSecurity.PayloadCapture558F01B60
import ShielddSecurity.PayloadCapture558F01B61
import ShielddSecurity.PayloadCapture558F01B62
import ShielddSecurity.PayloadCapture558F01B63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F01G07
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],6335,6840,6698⟩
def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F01B56.entries++PayloadCapture558F01B57.entries++PayloadCapture558F01B58.entries++PayloadCapture558F01B59.entries++PayloadCapture558F01B60.entries++PayloadCapture558F01B61.entries++PayloadCapture558F01B62.entries++PayloadCapture558F01B63.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F01B56.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B56.checked
  have h1 : PayloadCapture558F01B57.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B57.checked
  have h2 : PayloadCapture558F01B58.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B58.checked
  have h3 : PayloadCapture558F01B59.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B59.checked
  have h4 : PayloadCapture558F01B60.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B60.checked
  have h5 : PayloadCapture558F01B61.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B61.checked
  have h6 : PayloadCapture558F01B62.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B62.checked
  have h7 : PayloadCapture558F01B63.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B63.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 57 8 := by
  simp only [entries,List.map_append,PayloadCapture558F01B56.schedule,PayloadCapture558F01B57.schedule,PayloadCapture558F01B58.schedule,PayloadCapture558F01B59.schedule,PayloadCapture558F01B60.schedule,PayloadCapture558F01B61.schedule,PayloadCapture558F01B62.schedule,PayloadCapture558F01B63.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F01G07

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F01G07.checked
#print axioms ShielddSecurity.PayloadCapture558F01G07.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F01G07.schedule
#print axioms ShielddSecurity.PayloadCapture558F01G07.schedule
