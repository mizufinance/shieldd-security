-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F01G00
import ShielddSecurity.TierCapture610F01G01
import ShielddSecurity.TierCapture610F01G02
import ShielddSecurity.TierCapture610F01G03
import ShielddSecurity.TierCapture610F01G04
import ShielddSecurity.TierCapture610F01G05
import ShielddSecurity.TierCapture610F01G06
import ShielddSecurity.TierCapture610F01G07
import ShielddSecurity.TierCapture610F01G08
import ShielddSecurity.TierCapture610F01G09
import ShielddSecurity.TierCapture610F01G10
import ShielddSecurity.TierCapture610F01G11
import ShielddSecurity.TierCapture610F01G12
import ShielddSecurity.TierCapture610F01G13
import ShielddSecurity.TierCapture610F01G14
import ShielddSecurity.TierCapture610F01G15
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F01
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33792,1),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],11612,12873,12665⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F01G00.entries++TierCapture610F01G01.entries++TierCapture610F01G02.entries++TierCapture610F01G03.entries++TierCapture610F01G04.entries++TierCapture610F01G05.entries++TierCapture610F01G06.entries++TierCapture610F01G07.entries++TierCapture610F01G08.entries++TierCapture610F01G09.entries++TierCapture610F01G10.entries++TierCapture610F01G11.entries++TierCapture610F01G12.entries++TierCapture610F01G13.entries++TierCapture610F01G14.entries++TierCapture610F01G15.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F01G00.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G00.checked
  have h1 : TierCapture610F01G01.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G01.checked
  have h2 : TierCapture610F01G02.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G02.checked
  have h3 : TierCapture610F01G03.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G03.checked
  have h4 : TierCapture610F01G04.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G04.checked
  have h5 : TierCapture610F01G05.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G05.checked
  have h6 : TierCapture610F01G06.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G06.checked
  have h7 : TierCapture610F01G07.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G07.checked
  have h8 : TierCapture610F01G08.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G08.checked
  have h9 : TierCapture610F01G09.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G09.checked
  have h10 : TierCapture610F01G10.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G10.checked
  have h11 : TierCapture610F01G11.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G11.checked
  have h12 : TierCapture610F01G12.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G12.checked
  have h13 : TierCapture610F01G13.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G13.checked
  have h14 : TierCapture610F01G14.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G14.checked
  have h15 : TierCapture610F01G15.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F01G15.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 1 125 := by
  simp only [entries,List.map_append,TierCapture610F01G00.schedule,TierCapture610F01G01.schedule,TierCapture610F01G02.schedule,TierCapture610F01G03.schedule,TierCapture610F01G04.schedule,TierCapture610F01G05.schedule,TierCapture610F01G06.schedule,TierCapture610F01G07.schedule,TierCapture610F01G08.schedule,TierCapture610F01G09.schedule,TierCapture610F01G10.schedule,TierCapture610F01G11.schedule,TierCapture610F01G12.schedule,TierCapture610F01G13.schedule,TierCapture610F01G14.schedule,TierCapture610F01G15.schedule]
  rfl

end ShielddSecurity.TierCapture610F01

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01.checked
#print axioms ShielddSecurity.TierCapture610F01.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F01.schedule
#print axioms ShielddSecurity.TierCapture610F01.schedule
