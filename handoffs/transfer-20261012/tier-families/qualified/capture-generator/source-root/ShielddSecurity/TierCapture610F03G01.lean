-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F03B08
import ShielddSecurity.TierCapture610F03B09
import ShielddSecurity.TierCapture610F03B10
import ShielddSecurity.TierCapture610F03B11
import ShielddSecurity.TierCapture610F03B12
import ShielddSecurity.TierCapture610F03B13
import ShielddSecurity.TierCapture610F03B14
import ShielddSecurity.TierCapture610F03B15
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F03G01
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121566,1),(161679,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121568,1),(161681,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],14892,15397,15197⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F03B08.entries++TierCapture610F03B09.entries++TierCapture610F03B10.entries++TierCapture610F03B11.entries++TierCapture610F03B12.entries++TierCapture610F03B13.entries++TierCapture610F03B14.entries++TierCapture610F03B15.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F03B08.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B08.checked
  have h1 : TierCapture610F03B09.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B09.checked
  have h2 : TierCapture610F03B10.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B10.checked
  have h3 : TierCapture610F03B11.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B11.checked
  have h4 : TierCapture610F03B12.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B12.checked
  have h5 : TierCapture610F03B13.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B13.checked
  have h6 : TierCapture610F03B14.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B14.checked
  have h7 : TierCapture610F03B15.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B15.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 9 8 := by
  simp only [entries,List.map_append,TierCapture610F03B08.schedule,TierCapture610F03B09.schedule,TierCapture610F03B10.schedule,TierCapture610F03B11.schedule,TierCapture610F03B12.schedule,TierCapture610F03B13.schedule,TierCapture610F03B14.schedule,TierCapture610F03B15.schedule]
  rfl

end ShielddSecurity.TierCapture610F03G01

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F03G01.checked
#print axioms ShielddSecurity.TierCapture610F03G01.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F03G01.schedule
#print axioms ShielddSecurity.TierCapture610F03G01.schedule
