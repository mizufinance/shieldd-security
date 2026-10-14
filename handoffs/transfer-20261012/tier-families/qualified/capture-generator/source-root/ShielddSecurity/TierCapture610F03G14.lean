-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F03B112
import ShielddSecurity.TierCapture610F03B113
import ShielddSecurity.TierCapture610F03B114
import ShielddSecurity.TierCapture610F03B115
import ShielddSecurity.TierCapture610F03B116
import ShielddSecurity.TierCapture610F03B117
import ShielddSecurity.TierCapture610F03B118
import ShielddSecurity.TierCapture610F03B119
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F03G14
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121566,1),(161679,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121568,1),(161681,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],14892,15397,15197⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F03B112.entries++TierCapture610F03B113.entries++TierCapture610F03B114.entries++TierCapture610F03B115.entries++TierCapture610F03B116.entries++TierCapture610F03B117.entries++TierCapture610F03B118.entries++TierCapture610F03B119.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F03B112.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B112.checked
  have h1 : TierCapture610F03B113.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B113.checked
  have h2 : TierCapture610F03B114.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B114.checked
  have h3 : TierCapture610F03B115.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B115.checked
  have h4 : TierCapture610F03B116.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B116.checked
  have h5 : TierCapture610F03B117.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B117.checked
  have h6 : TierCapture610F03B118.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B118.checked
  have h7 : TierCapture610F03B119.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F03B119.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 113 8 := by
  simp only [entries,List.map_append,TierCapture610F03B112.schedule,TierCapture610F03B113.schedule,TierCapture610F03B114.schedule,TierCapture610F03B115.schedule,TierCapture610F03B116.schedule,TierCapture610F03B117.schedule,TierCapture610F03B118.schedule,TierCapture610F03B119.schedule]
  rfl

end ShielddSecurity.TierCapture610F03G14

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F03G14.checked
#print axioms ShielddSecurity.TierCapture610F03G14.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F03G14.schedule
#print axioms ShielddSecurity.TierCapture610F03G14.schedule
