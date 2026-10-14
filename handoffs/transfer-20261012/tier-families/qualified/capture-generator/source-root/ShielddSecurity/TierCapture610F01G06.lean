-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F01B48
import ShielddSecurity.TierCapture610F01B49
import ShielddSecurity.TierCapture610F01B50
import ShielddSecurity.TierCapture610F01B51
import ShielddSecurity.TierCapture610F01B52
import ShielddSecurity.TierCapture610F01B53
import ShielddSecurity.TierCapture610F01B54
import ShielddSecurity.TierCapture610F01B55
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F01G06
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],11612,12873,12665⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F01B48.entries++TierCapture610F01B49.entries++TierCapture610F01B50.entries++TierCapture610F01B51.entries++TierCapture610F01B52.entries++TierCapture610F01B53.entries++TierCapture610F01B54.entries++TierCapture610F01B55.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F01B48.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B48.checked
  have h1 : TierCapture610F01B49.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B49.checked
  have h2 : TierCapture610F01B50.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B50.checked
  have h3 : TierCapture610F01B51.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B51.checked
  have h4 : TierCapture610F01B52.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B52.checked
  have h5 : TierCapture610F01B53.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B53.checked
  have h6 : TierCapture610F01B54.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B54.checked
  have h7 : TierCapture610F01B55.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B55.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 49 8 := by
  simp only [entries,List.map_append,TierCapture610F01B48.schedule,TierCapture610F01B49.schedule,TierCapture610F01B50.schedule,TierCapture610F01B51.schedule,TierCapture610F01B52.schedule,TierCapture610F01B53.schedule,TierCapture610F01B54.schedule,TierCapture610F01B55.schedule]
  rfl

end ShielddSecurity.TierCapture610F01G06

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G06.checked
#print axioms ShielddSecurity.TierCapture610F01G06.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G06.schedule
#print axioms ShielddSecurity.TierCapture610F01G06.schedule
