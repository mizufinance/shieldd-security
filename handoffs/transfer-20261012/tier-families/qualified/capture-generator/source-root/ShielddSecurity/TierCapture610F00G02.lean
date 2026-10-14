-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F00B16
import ShielddSecurity.TierCapture610F00B17
import ShielddSecurity.TierCapture610F00B18
import ShielddSecurity.TierCapture610F00B19
import ShielddSecurity.TierCapture610F00B20
import ShielddSecurity.TierCapture610F00B21
import ShielddSecurity.TierCapture610F00B22
import ShielddSecurity.TierCapture610F00B23
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F00G02
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121566,1),(142312,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121568,1),(142314,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],11612,12117,11909⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F00B16.entries++TierCapture610F00B17.entries++TierCapture610F00B18.entries++TierCapture610F00B19.entries++TierCapture610F00B20.entries++TierCapture610F00B21.entries++TierCapture610F00B22.entries++TierCapture610F00B23.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F00B16.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B16.checked
  have h1 : TierCapture610F00B17.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B17.checked
  have h2 : TierCapture610F00B18.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B18.checked
  have h3 : TierCapture610F00B19.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B19.checked
  have h4 : TierCapture610F00B20.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B20.checked
  have h5 : TierCapture610F00B21.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B21.checked
  have h6 : TierCapture610F00B22.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B22.checked
  have h7 : TierCapture610F00B23.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00B23.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 17 8 := by
  simp only [entries,List.map_append,TierCapture610F00B16.schedule,TierCapture610F00B17.schedule,TierCapture610F00B18.schedule,TierCapture610F00B19.schedule,TierCapture610F00B20.schedule,TierCapture610F00B21.schedule,TierCapture610F00B22.schedule,TierCapture610F00B23.schedule]
  rfl

end ShielddSecurity.TierCapture610F00G02

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F00G02.checked
#print axioms ShielddSecurity.TierCapture610F00G02.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F00G02.schedule
#print axioms ShielddSecurity.TierCapture610F00G02.schedule
