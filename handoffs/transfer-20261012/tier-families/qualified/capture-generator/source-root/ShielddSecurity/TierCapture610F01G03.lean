-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F01B24
import ShielddSecurity.TierCapture610F01B25
import ShielddSecurity.TierCapture610F01B26
import ShielddSecurity.TierCapture610F01B27
import ShielddSecurity.TierCapture610F01B28
import ShielddSecurity.TierCapture610F01B29
import ShielddSecurity.TierCapture610F01B30
import ShielddSecurity.TierCapture610F01B31
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F01G03
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],11612,12873,12665⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F01B24.entries++TierCapture610F01B25.entries++TierCapture610F01B26.entries++TierCapture610F01B27.entries++TierCapture610F01B28.entries++TierCapture610F01B29.entries++TierCapture610F01B30.entries++TierCapture610F01B31.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F01B24.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B24.checked
  have h1 : TierCapture610F01B25.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B25.checked
  have h2 : TierCapture610F01B26.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B26.checked
  have h3 : TierCapture610F01B27.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B27.checked
  have h4 : TierCapture610F01B28.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B28.checked
  have h5 : TierCapture610F01B29.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B29.checked
  have h6 : TierCapture610F01B30.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B30.checked
  have h7 : TierCapture610F01B31.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B31.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 25 8 := by
  simp only [entries,List.map_append,TierCapture610F01B24.schedule,TierCapture610F01B25.schedule,TierCapture610F01B26.schedule,TierCapture610F01B27.schedule,TierCapture610F01B28.schedule,TierCapture610F01B29.schedule,TierCapture610F01B30.schedule,TierCapture610F01B31.schedule]
  rfl

end ShielddSecurity.TierCapture610F01G03

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G03.checked
#print axioms ShielddSecurity.TierCapture610F01G03.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G03.schedule
#print axioms ShielddSecurity.TierCapture610F01G03.schedule
