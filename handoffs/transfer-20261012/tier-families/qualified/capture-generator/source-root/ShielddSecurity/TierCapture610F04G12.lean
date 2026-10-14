-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F04B96
import ShielddSecurity.TierCapture610F04B97
import ShielddSecurity.TierCapture610F04B98
import ShielddSecurity.TierCapture610F04B99
import ShielddSecurity.TierCapture610F04B100
import ShielddSecurity.TierCapture610F04B101
import ShielddSecurity.TierCapture610F04B102
import ShielddSecurity.TierCapture610F04B103
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F04G12
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121566,1),(168972,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121568,1),(168974,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],16154,16659,16463⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F04B96.entries++TierCapture610F04B97.entries++TierCapture610F04B98.entries++TierCapture610F04B99.entries++TierCapture610F04B100.entries++TierCapture610F04B101.entries++TierCapture610F04B102.entries++TierCapture610F04B103.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F04B96.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F04B96.checked
  have h1 : TierCapture610F04B97.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F04B97.checked
  have h2 : TierCapture610F04B98.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F04B98.checked
  have h3 : TierCapture610F04B99.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F04B99.checked
  have h4 : TierCapture610F04B100.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F04B100.checked
  have h5 : TierCapture610F04B101.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F04B101.checked
  have h6 : TierCapture610F04B102.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F04B102.checked
  have h7 : TierCapture610F04B103.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F04B103.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 97 8 := by
  simp only [entries,List.map_append,TierCapture610F04B96.schedule,TierCapture610F04B97.schedule,TierCapture610F04B98.schedule,TierCapture610F04B99.schedule,TierCapture610F04B100.schedule,TierCapture610F04B101.schedule,TierCapture610F04B102.schedule,TierCapture610F04B103.schedule]
  rfl

end ShielddSecurity.TierCapture610F04G12

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F04G12.checked
#print axioms ShielddSecurity.TierCapture610F04G12.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F04G12.schedule
#print axioms ShielddSecurity.TierCapture610F04G12.schedule
