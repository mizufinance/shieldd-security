-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F01B56
import ShielddSecurity.TierCapture610F01B57
import ShielddSecurity.TierCapture610F01B58
import ShielddSecurity.TierCapture610F01B59
import ShielddSecurity.TierCapture610F01B60
import ShielddSecurity.TierCapture610F01B61
import ShielddSecurity.TierCapture610F01B62
import ShielddSecurity.TierCapture610F01B63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F01G07
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],11612,12873,12665⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F01B56.entries++TierCapture610F01B57.entries++TierCapture610F01B58.entries++TierCapture610F01B59.entries++TierCapture610F01B60.entries++TierCapture610F01B61.entries++TierCapture610F01B62.entries++TierCapture610F01B63.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F01B56.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B56.checked
  have h1 : TierCapture610F01B57.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B57.checked
  have h2 : TierCapture610F01B58.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B58.checked
  have h3 : TierCapture610F01B59.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B59.checked
  have h4 : TierCapture610F01B60.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B60.checked
  have h5 : TierCapture610F01B61.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B61.checked
  have h6 : TierCapture610F01B62.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B62.checked
  have h7 : TierCapture610F01B63.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B63.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 57 8 := by
  simp only [entries,List.map_append,TierCapture610F01B56.schedule,TierCapture610F01B57.schedule,TierCapture610F01B58.schedule,TierCapture610F01B59.schedule,TierCapture610F01B60.schedule,TierCapture610F01B61.schedule,TierCapture610F01B62.schedule,TierCapture610F01B63.schedule]
  rfl

end ShielddSecurity.TierCapture610F01G07

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G07.checked
#print axioms ShielddSecurity.TierCapture610F01G07.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G07.schedule
#print axioms ShielddSecurity.TierCapture610F01G07.schedule
