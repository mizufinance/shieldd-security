-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F00B80
import ShielddSecurity.TierCapture610F00B81
import ShielddSecurity.TierCapture610F00B82
import ShielddSecurity.TierCapture610F00B83
import ShielddSecurity.TierCapture610F00B84
import ShielddSecurity.TierCapture610F00B85
import ShielddSecurity.TierCapture610F00B86
import ShielddSecurity.TierCapture610F00B87
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F00G10
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121566,1),(142312,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121568,1),(142314,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],11612,12117,11909⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F00B80.entries++TierCapture610F00B81.entries++TierCapture610F00B82.entries++TierCapture610F00B83.entries++TierCapture610F00B84.entries++TierCapture610F00B85.entries++TierCapture610F00B86.entries++TierCapture610F00B87.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F00B80.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B80.checked
  have h1 : TierCapture610F00B81.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B81.checked
  have h2 : TierCapture610F00B82.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B82.checked
  have h3 : TierCapture610F00B83.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B83.checked
  have h4 : TierCapture610F00B84.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B84.checked
  have h5 : TierCapture610F00B85.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B85.checked
  have h6 : TierCapture610F00B86.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B86.checked
  have h7 : TierCapture610F00B87.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B87.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 81 8 := by
  simp only [entries,List.map_append,TierCapture610F00B80.schedule,TierCapture610F00B81.schedule,TierCapture610F00B82.schedule,TierCapture610F00B83.schedule,TierCapture610F00B84.schedule,TierCapture610F00B85.schedule,TierCapture610F00B86.schedule,TierCapture610F00B87.schedule]
  rfl

end ShielddSecurity.TierCapture610F00G10

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F00G10.checked
#print axioms ShielddSecurity.TierCapture610F00G10.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F00G10.schedule
#print axioms ShielddSecurity.TierCapture610F00G10.schedule
