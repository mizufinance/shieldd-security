-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F01B104
import ShielddSecurity.PayloadCapture558F01B105
import ShielddSecurity.PayloadCapture558F01B106
import ShielddSecurity.PayloadCapture558F01B107
import ShielddSecurity.PayloadCapture558F01B108
import ShielddSecurity.PayloadCapture558F01B109
import ShielddSecurity.PayloadCapture558F01B110
import ShielddSecurity.PayloadCapture558F01B111
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F01G13
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],6335,6840,6698⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F01B104.entries++PayloadCapture558F01B105.entries++PayloadCapture558F01B106.entries++PayloadCapture558F01B107.entries++PayloadCapture558F01B108.entries++PayloadCapture558F01B109.entries++PayloadCapture558F01B110.entries++PayloadCapture558F01B111.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F01B104.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B104.checked
  have h1 : PayloadCapture558F01B105.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B105.checked
  have h2 : PayloadCapture558F01B106.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B106.checked
  have h3 : PayloadCapture558F01B107.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B107.checked
  have h4 : PayloadCapture558F01B108.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B108.checked
  have h5 : PayloadCapture558F01B109.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B109.checked
  have h6 : PayloadCapture558F01B110.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B110.checked
  have h7 : PayloadCapture558F01B111.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F01B111.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 105 8 := by
  simp only [entries,List.map_append,PayloadCapture558F01B104.schedule,PayloadCapture558F01B105.schedule,PayloadCapture558F01B106.schedule,PayloadCapture558F01B107.schedule,PayloadCapture558F01B108.schedule,PayloadCapture558F01B109.schedule,PayloadCapture558F01B110.schedule,PayloadCapture558F01B111.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F01G13

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F01G13.checked
#print axioms ShielddSecurity.PayloadCapture558F01G13.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F01G13.schedule
#print axioms ShielddSecurity.PayloadCapture558F01G13.schedule
