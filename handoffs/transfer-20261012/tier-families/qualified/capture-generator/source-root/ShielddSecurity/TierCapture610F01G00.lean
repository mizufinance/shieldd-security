-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F01B00
import ShielddSecurity.TierCapture610F01B01
import ShielddSecurity.TierCapture610F01B02
import ShielddSecurity.TierCapture610F01B03
import ShielddSecurity.TierCapture610F01B04
import ShielddSecurity.TierCapture610F01B05
import ShielddSecurity.TierCapture610F01B06
import ShielddSecurity.TierCapture610F01B07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F01G00
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],11612,12873,12665⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F01B00.entries++TierCapture610F01B01.entries++TierCapture610F01B02.entries++TierCapture610F01B03.entries++TierCapture610F01B04.entries++TierCapture610F01B05.entries++TierCapture610F01B06.entries++TierCapture610F01B07.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F01B00.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B00.checked
  have h1 : TierCapture610F01B01.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B01.checked
  have h2 : TierCapture610F01B02.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B02.checked
  have h3 : TierCapture610F01B03.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B03.checked
  have h4 : TierCapture610F01B04.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B04.checked
  have h5 : TierCapture610F01B05.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B05.checked
  have h6 : TierCapture610F01B06.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B06.checked
  have h7 : TierCapture610F01B07.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B07.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 1 8 := by
  simp only [entries,List.map_append,TierCapture610F01B00.schedule,TierCapture610F01B01.schedule,TierCapture610F01B02.schedule,TierCapture610F01B03.schedule,TierCapture610F01B04.schedule,TierCapture610F01B05.schedule,TierCapture610F01B06.schedule,TierCapture610F01B07.schedule]
  rfl

end ShielddSecurity.TierCapture610F01G00

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G00.checked
#print axioms ShielddSecurity.TierCapture610F01G00.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G00.schedule
#print axioms ShielddSecurity.TierCapture610F01G00.schedule
