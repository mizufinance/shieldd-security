-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F01B16
import ShielddSecurity.PayloadCapture558F01B17
import ShielddSecurity.PayloadCapture558F01B18
import ShielddSecurity.PayloadCapture558F01B19
import ShielddSecurity.PayloadCapture558F01B20
import ShielddSecurity.PayloadCapture558F01B21
import ShielddSecurity.PayloadCapture558F01B22
import ShielddSecurity.PayloadCapture558F01B23
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F01G02
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],6335,6840,6698⟩
def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F01B16.entries++PayloadCapture558F01B17.entries++PayloadCapture558F01B18.entries++PayloadCapture558F01B19.entries++PayloadCapture558F01B20.entries++PayloadCapture558F01B21.entries++PayloadCapture558F01B22.entries++PayloadCapture558F01B23.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F01B16.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B16.checked
  have h1 : PayloadCapture558F01B17.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B17.checked
  have h2 : PayloadCapture558F01B18.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B18.checked
  have h3 : PayloadCapture558F01B19.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B19.checked
  have h4 : PayloadCapture558F01B20.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B20.checked
  have h5 : PayloadCapture558F01B21.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B21.checked
  have h6 : PayloadCapture558F01B22.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B22.checked
  have h7 : PayloadCapture558F01B23.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B23.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 17 8 := by
  simp only [entries,List.map_append,PayloadCapture558F01B16.schedule,PayloadCapture558F01B17.schedule,PayloadCapture558F01B18.schedule,PayloadCapture558F01B19.schedule,PayloadCapture558F01B20.schedule,PayloadCapture558F01B21.schedule,PayloadCapture558F01B22.schedule,PayloadCapture558F01B23.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F01G02

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F01G02.checked
#print axioms ShielddSecurity.PayloadCapture558F01G02.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F01G02.schedule
#print axioms ShielddSecurity.PayloadCapture558F01G02.schedule
