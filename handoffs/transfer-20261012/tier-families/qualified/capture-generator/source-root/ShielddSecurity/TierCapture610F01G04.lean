-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F01B32
import ShielddSecurity.TierCapture610F01B33
import ShielddSecurity.TierCapture610F01B34
import ShielddSecurity.TierCapture610F01B35
import ShielddSecurity.TierCapture610F01B36
import ShielddSecurity.TierCapture610F01B37
import ShielddSecurity.TierCapture610F01B38
import ShielddSecurity.TierCapture610F01B39
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F01G04
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],11612,12873,12665⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F01B32.entries++TierCapture610F01B33.entries++TierCapture610F01B34.entries++TierCapture610F01B35.entries++TierCapture610F01B36.entries++TierCapture610F01B37.entries++TierCapture610F01B38.entries++TierCapture610F01B39.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F01B32.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B32.checked
  have h1 : TierCapture610F01B33.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B33.checked
  have h2 : TierCapture610F01B34.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B34.checked
  have h3 : TierCapture610F01B35.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B35.checked
  have h4 : TierCapture610F01B36.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B36.checked
  have h5 : TierCapture610F01B37.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B37.checked
  have h6 : TierCapture610F01B38.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B38.checked
  have h7 : TierCapture610F01B39.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B39.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 33 8 := by
  simp only [entries,List.map_append,TierCapture610F01B32.schedule,TierCapture610F01B33.schedule,TierCapture610F01B34.schedule,TierCapture610F01B35.schedule,TierCapture610F01B36.schedule,TierCapture610F01B37.schedule,TierCapture610F01B38.schedule,TierCapture610F01B39.schedule]
  rfl

end ShielddSecurity.TierCapture610F01G04

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G04.checked
#print axioms ShielddSecurity.TierCapture610F01G04.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G04.schedule
#print axioms ShielddSecurity.TierCapture610F01G04.schedule
