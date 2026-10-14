-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F01B64
import ShielddSecurity.TierCapture610F01B65
import ShielddSecurity.TierCapture610F01B66
import ShielddSecurity.TierCapture610F01B67
import ShielddSecurity.TierCapture610F01B68
import ShielddSecurity.TierCapture610F01B69
import ShielddSecurity.TierCapture610F01B70
import ShielddSecurity.TierCapture610F01B71
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F01G08
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],11612,12873,12665⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F01B64.entries++TierCapture610F01B65.entries++TierCapture610F01B66.entries++TierCapture610F01B67.entries++TierCapture610F01B68.entries++TierCapture610F01B69.entries++TierCapture610F01B70.entries++TierCapture610F01B71.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F01B64.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B64.checked
  have h1 : TierCapture610F01B65.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B65.checked
  have h2 : TierCapture610F01B66.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B66.checked
  have h3 : TierCapture610F01B67.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B67.checked
  have h4 : TierCapture610F01B68.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B68.checked
  have h5 : TierCapture610F01B69.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B69.checked
  have h6 : TierCapture610F01B70.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B70.checked
  have h7 : TierCapture610F01B71.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B71.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 65 8 := by
  simp only [entries,List.map_append,TierCapture610F01B64.schedule,TierCapture610F01B65.schedule,TierCapture610F01B66.schedule,TierCapture610F01B67.schedule,TierCapture610F01B68.schedule,TierCapture610F01B69.schedule,TierCapture610F01B70.schedule,TierCapture610F01B71.schedule]
  rfl

end ShielddSecurity.TierCapture610F01G08

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G08.checked
#print axioms ShielddSecurity.TierCapture610F01G08.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G08.schedule
#print axioms ShielddSecurity.TierCapture610F01G08.schedule
