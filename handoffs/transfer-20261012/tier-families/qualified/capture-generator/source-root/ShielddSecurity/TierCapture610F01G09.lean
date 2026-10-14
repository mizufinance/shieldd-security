-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F01B72
import ShielddSecurity.TierCapture610F01B73
import ShielddSecurity.TierCapture610F01B74
import ShielddSecurity.TierCapture610F01B75
import ShielddSecurity.TierCapture610F01B76
import ShielddSecurity.TierCapture610F01B77
import ShielddSecurity.TierCapture610F01B78
import ShielddSecurity.TierCapture610F01B79
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F01G09
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],11612,12873,12665⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F01B72.entries++TierCapture610F01B73.entries++TierCapture610F01B74.entries++TierCapture610F01B75.entries++TierCapture610F01B76.entries++TierCapture610F01B77.entries++TierCapture610F01B78.entries++TierCapture610F01B79.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F01B72.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B72.checked
  have h1 : TierCapture610F01B73.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B73.checked
  have h2 : TierCapture610F01B74.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B74.checked
  have h3 : TierCapture610F01B75.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B75.checked
  have h4 : TierCapture610F01B76.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B76.checked
  have h5 : TierCapture610F01B77.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B77.checked
  have h6 : TierCapture610F01B78.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B78.checked
  have h7 : TierCapture610F01B79.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B79.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 73 8 := by
  simp only [entries,List.map_append,TierCapture610F01B72.schedule,TierCapture610F01B73.schedule,TierCapture610F01B74.schedule,TierCapture610F01B75.schedule,TierCapture610F01B76.schedule,TierCapture610F01B77.schedule,TierCapture610F01B78.schedule,TierCapture610F01B79.schedule]
  rfl

end ShielddSecurity.TierCapture610F01G09

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G09.checked
#print axioms ShielddSecurity.TierCapture610F01G09.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G09.schedule
#print axioms ShielddSecurity.TierCapture610F01G09.schedule
