-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F01B96
import ShielddSecurity.TierCapture610F01B97
import ShielddSecurity.TierCapture610F01B98
import ShielddSecurity.TierCapture610F01B99
import ShielddSecurity.TierCapture610F01B100
import ShielddSecurity.TierCapture610F01B101
import ShielddSecurity.TierCapture610F01B102
import ShielddSecurity.TierCapture610F01B103
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F01G12
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],11612,12873,12665⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F01B96.entries++TierCapture610F01B97.entries++TierCapture610F01B98.entries++TierCapture610F01B99.entries++TierCapture610F01B100.entries++TierCapture610F01B101.entries++TierCapture610F01B102.entries++TierCapture610F01B103.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F01B96.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B96.checked
  have h1 : TierCapture610F01B97.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B97.checked
  have h2 : TierCapture610F01B98.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B98.checked
  have h3 : TierCapture610F01B99.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B99.checked
  have h4 : TierCapture610F01B100.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B100.checked
  have h5 : TierCapture610F01B101.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B101.checked
  have h6 : TierCapture610F01B102.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B102.checked
  have h7 : TierCapture610F01B103.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B103.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 97 8 := by
  simp only [entries,List.map_append,TierCapture610F01B96.schedule,TierCapture610F01B97.schedule,TierCapture610F01B98.schedule,TierCapture610F01B99.schedule,TierCapture610F01B100.schedule,TierCapture610F01B101.schedule,TierCapture610F01B102.schedule,TierCapture610F01B103.schedule]
  rfl

end ShielddSecurity.TierCapture610F01G12

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G12.checked
#print axioms ShielddSecurity.TierCapture610F01G12.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G12.schedule
#print axioms ShielddSecurity.TierCapture610F01G12.schedule
