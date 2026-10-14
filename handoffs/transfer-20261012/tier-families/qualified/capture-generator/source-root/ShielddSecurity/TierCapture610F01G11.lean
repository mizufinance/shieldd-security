-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F01B88
import ShielddSecurity.TierCapture610F01B89
import ShielddSecurity.TierCapture610F01B90
import ShielddSecurity.TierCapture610F01B91
import ShielddSecurity.TierCapture610F01B92
import ShielddSecurity.TierCapture610F01B93
import ShielddSecurity.TierCapture610F01B94
import ShielddSecurity.TierCapture610F01B95
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F01G11
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],11612,12873,12665⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F01B88.entries++TierCapture610F01B89.entries++TierCapture610F01B90.entries++TierCapture610F01B91.entries++TierCapture610F01B92.entries++TierCapture610F01B93.entries++TierCapture610F01B94.entries++TierCapture610F01B95.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F01B88.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B88.checked
  have h1 : TierCapture610F01B89.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B89.checked
  have h2 : TierCapture610F01B90.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B90.checked
  have h3 : TierCapture610F01B91.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B91.checked
  have h4 : TierCapture610F01B92.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B92.checked
  have h5 : TierCapture610F01B93.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B93.checked
  have h6 : TierCapture610F01B94.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B94.checked
  have h7 : TierCapture610F01B95.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01B95.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 89 8 := by
  simp only [entries,List.map_append,TierCapture610F01B88.schedule,TierCapture610F01B89.schedule,TierCapture610F01B90.schedule,TierCapture610F01B91.schedule,TierCapture610F01B92.schedule,TierCapture610F01B93.schedule,TierCapture610F01B94.schedule,TierCapture610F01B95.schedule]
  rfl

end ShielddSecurity.TierCapture610F01G11

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G11.checked
#print axioms ShielddSecurity.TierCapture610F01G11.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01G11.schedule
#print axioms ShielddSecurity.TierCapture610F01G11.schedule
