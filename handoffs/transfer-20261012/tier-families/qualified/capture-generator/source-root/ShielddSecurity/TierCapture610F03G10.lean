-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F03B80
import ShielddSecurity.TierCapture610F03B81
import ShielddSecurity.TierCapture610F03B82
import ShielddSecurity.TierCapture610F03B83
import ShielddSecurity.TierCapture610F03B84
import ShielddSecurity.TierCapture610F03B85
import ShielddSecurity.TierCapture610F03B86
import ShielddSecurity.TierCapture610F03B87
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F03G10
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121566,1),(161679,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121568,1),(161681,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],14892,15397,15197⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F03B80.entries++TierCapture610F03B81.entries++TierCapture610F03B82.entries++TierCapture610F03B83.entries++TierCapture610F03B84.entries++TierCapture610F03B85.entries++TierCapture610F03B86.entries++TierCapture610F03B87.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F03B80.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B80.checked
  have h1 : TierCapture610F03B81.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B81.checked
  have h2 : TierCapture610F03B82.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B82.checked
  have h3 : TierCapture610F03B83.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B83.checked
  have h4 : TierCapture610F03B84.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B84.checked
  have h5 : TierCapture610F03B85.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B85.checked
  have h6 : TierCapture610F03B86.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B86.checked
  have h7 : TierCapture610F03B87.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B87.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 81 8 := by
  simp only [entries,List.map_append,TierCapture610F03B80.schedule,TierCapture610F03B81.schedule,TierCapture610F03B82.schedule,TierCapture610F03B83.schedule,TierCapture610F03B84.schedule,TierCapture610F03B85.schedule,TierCapture610F03B86.schedule,TierCapture610F03B87.schedule]
  rfl

end ShielddSecurity.TierCapture610F03G10

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F03G10.checked
#print axioms ShielddSecurity.TierCapture610F03G10.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F03G10.schedule
#print axioms ShielddSecurity.TierCapture610F03G10.schedule
