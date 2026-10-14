-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F01B40
import ShielddSecurity.TierCapture610F01B41
import ShielddSecurity.TierCapture610F01B42
import ShielddSecurity.TierCapture610F01B43
import ShielddSecurity.TierCapture610F01B44
import ShielddSecurity.TierCapture610F01B45
import ShielddSecurity.TierCapture610F01B46
import ShielddSecurity.TierCapture610F01B47
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F01G05
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],11612,12873,12665⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F01B40.entries++TierCapture610F01B41.entries++TierCapture610F01B42.entries++TierCapture610F01B43.entries++TierCapture610F01B44.entries++TierCapture610F01B45.entries++TierCapture610F01B46.entries++TierCapture610F01B47.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F01B40.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B40.checked
  have h1 : TierCapture610F01B41.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B41.checked
  have h2 : TierCapture610F01B42.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B42.checked
  have h3 : TierCapture610F01B43.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B43.checked
  have h4 : TierCapture610F01B44.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B44.checked
  have h5 : TierCapture610F01B45.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B45.checked
  have h6 : TierCapture610F01B46.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B46.checked
  have h7 : TierCapture610F01B47.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B47.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 41 8 := by
  simp only [entries,List.map_append,TierCapture610F01B40.schedule,TierCapture610F01B41.schedule,TierCapture610F01B42.schedule,TierCapture610F01B43.schedule,TierCapture610F01B44.schedule,TierCapture610F01B45.schedule,TierCapture610F01B46.schedule,TierCapture610F01B47.schedule]
  rfl

end ShielddSecurity.TierCapture610F01G05

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G05.checked
#print axioms ShielddSecurity.TierCapture610F01G05.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G05.schedule
#print axioms ShielddSecurity.TierCapture610F01G05.schedule
