-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F02B120
import ShielddSecurity.TierCapture610F02B121
import ShielddSecurity.TierCapture610F02B122
import ShielddSecurity.TierCapture610F02B123
import ShielddSecurity.TierCapture610F02B124
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F02G15
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121566,1),(154386,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121568,1),(154388,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],13630,14135,13931⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F02B120.entries++TierCapture610F02B121.entries++TierCapture610F02B122.entries++TierCapture610F02B123.entries++TierCapture610F02B124.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F02B120.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B120.checked
  have h1 : TierCapture610F02B121.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B121.checked
  have h2 : TierCapture610F02B122.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B122.checked
  have h3 : TierCapture610F02B123.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B123.checked
  have h4 : TierCapture610F02B124.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B124.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 121 5 := by
  simp only [entries,List.map_append,TierCapture610F02B120.schedule,TierCapture610F02B121.schedule,TierCapture610F02B122.schedule,TierCapture610F02B123.schedule,TierCapture610F02B124.schedule]
  rfl

end ShielddSecurity.TierCapture610F02G15

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F02G15.checked
#print axioms ShielddSecurity.TierCapture610F02G15.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F02G15.schedule
#print axioms ShielddSecurity.TierCapture610F02G15.schedule
