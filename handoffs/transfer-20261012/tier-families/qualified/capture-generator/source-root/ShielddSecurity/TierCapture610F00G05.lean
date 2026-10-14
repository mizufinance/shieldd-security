-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F00B40
import ShielddSecurity.TierCapture610F00B41
import ShielddSecurity.TierCapture610F00B42
import ShielddSecurity.TierCapture610F00B43
import ShielddSecurity.TierCapture610F00B44
import ShielddSecurity.TierCapture610F00B45
import ShielddSecurity.TierCapture610F00B46
import ShielddSecurity.TierCapture610F00B47
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F00G05
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121566,1),(142312,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121568,1),(142314,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],11612,12117,11909⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F00B40.entries++TierCapture610F00B41.entries++TierCapture610F00B42.entries++TierCapture610F00B43.entries++TierCapture610F00B44.entries++TierCapture610F00B45.entries++TierCapture610F00B46.entries++TierCapture610F00B47.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F00B40.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B40.checked
  have h1 : TierCapture610F00B41.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B41.checked
  have h2 : TierCapture610F00B42.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B42.checked
  have h3 : TierCapture610F00B43.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B43.checked
  have h4 : TierCapture610F00B44.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B44.checked
  have h5 : TierCapture610F00B45.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B45.checked
  have h6 : TierCapture610F00B46.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B46.checked
  have h7 : TierCapture610F00B47.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B47.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 41 8 := by
  simp only [entries,List.map_append,TierCapture610F00B40.schedule,TierCapture610F00B41.schedule,TierCapture610F00B42.schedule,TierCapture610F00B43.schedule,TierCapture610F00B44.schedule,TierCapture610F00B45.schedule,TierCapture610F00B46.schedule,TierCapture610F00B47.schedule]
  rfl

end ShielddSecurity.TierCapture610F00G05

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F00G05.checked
#print axioms ShielddSecurity.TierCapture610F00G05.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F00G05.schedule
#print axioms ShielddSecurity.TierCapture610F00G05.schedule
