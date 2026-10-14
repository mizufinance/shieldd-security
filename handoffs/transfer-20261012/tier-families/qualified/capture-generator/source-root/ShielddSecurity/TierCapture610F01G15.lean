-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F01B120
import ShielddSecurity.TierCapture610F01B121
import ShielddSecurity.TierCapture610F01B122
import ShielddSecurity.TierCapture610F01B123
import ShielddSecurity.TierCapture610F01B124
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F01G15
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],11612,12873,12665⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F01B120.entries++TierCapture610F01B121.entries++TierCapture610F01B122.entries++TierCapture610F01B123.entries++TierCapture610F01B124.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F01B120.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B120.checked
  have h1 : TierCapture610F01B121.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B121.checked
  have h2 : TierCapture610F01B122.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B122.checked
  have h3 : TierCapture610F01B123.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B123.checked
  have h4 : TierCapture610F01B124.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B124.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 121 5 := by
  simp only [entries,List.map_append,TierCapture610F01B120.schedule,TierCapture610F01B121.schedule,TierCapture610F01B122.schedule,TierCapture610F01B123.schedule,TierCapture610F01B124.schedule]
  rfl

end ShielddSecurity.TierCapture610F01G15

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G15.checked
#print axioms ShielddSecurity.TierCapture610F01G15.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G15.schedule
#print axioms ShielddSecurity.TierCapture610F01G15.schedule
