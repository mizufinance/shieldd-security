-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F02B64
import ShielddSecurity.TierCapture610F02B65
import ShielddSecurity.TierCapture610F02B66
import ShielddSecurity.TierCapture610F02B67
import ShielddSecurity.TierCapture610F02B68
import ShielddSecurity.TierCapture610F02B69
import ShielddSecurity.TierCapture610F02B70
import ShielddSecurity.TierCapture610F02B71
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F02G08
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121566,1),(154386,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121568,1),(154388,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],13630,14135,13931⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F02B64.entries++TierCapture610F02B65.entries++TierCapture610F02B66.entries++TierCapture610F02B67.entries++TierCapture610F02B68.entries++TierCapture610F02B69.entries++TierCapture610F02B70.entries++TierCapture610F02B71.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F02B64.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B64.checked
  have h1 : TierCapture610F02B65.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B65.checked
  have h2 : TierCapture610F02B66.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B66.checked
  have h3 : TierCapture610F02B67.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B67.checked
  have h4 : TierCapture610F02B68.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B68.checked
  have h5 : TierCapture610F02B69.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B69.checked
  have h6 : TierCapture610F02B70.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B70.checked
  have h7 : TierCapture610F02B71.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F02B71.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 65 8 := by
  simp only [entries,List.map_append,TierCapture610F02B64.schedule,TierCapture610F02B65.schedule,TierCapture610F02B66.schedule,TierCapture610F02B67.schedule,TierCapture610F02B68.schedule,TierCapture610F02B69.schedule,TierCapture610F02B70.schedule,TierCapture610F02B71.schedule]
  rfl

end ShielddSecurity.TierCapture610F02G08

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F02G08.checked
#print axioms ShielddSecurity.TierCapture610F02G08.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F02G08.schedule
#print axioms ShielddSecurity.TierCapture610F02G08.schedule
