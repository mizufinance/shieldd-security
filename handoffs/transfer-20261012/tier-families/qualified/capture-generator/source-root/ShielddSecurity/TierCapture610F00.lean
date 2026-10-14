-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.TierCapture610F00G00
import ShielddSecurity.TierCapture610F00G01
import ShielddSecurity.TierCapture610F00G02
import ShielddSecurity.TierCapture610F00G03
import ShielddSecurity.TierCapture610F00G04
import ShielddSecurity.TierCapture610F00G05
import ShielddSecurity.TierCapture610F00G06
import ShielddSecurity.TierCapture610F00G07
import ShielddSecurity.TierCapture610F00G08
import ShielddSecurity.TierCapture610F00G09
import ShielddSecurity.TierCapture610F00G10
import ShielddSecurity.TierCapture610F00G11
import ShielddSecurity.TierCapture610F00G12
import ShielddSecurity.TierCapture610F00G13
import ShielddSecurity.TierCapture610F00G14
import ShielddSecurity.TierCapture610F00G15
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierCapture610F00
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121566,1),(142312,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121568,1),(142314,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],11612,12117,11909⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := TierCapture610F00G00.entries++TierCapture610F00G01.entries++TierCapture610F00G02.entries++TierCapture610F00G03.entries++TierCapture610F00G04.entries++TierCapture610F00G05.entries++TierCapture610F00G06.entries++TierCapture610F00G07.entries++TierCapture610F00G08.entries++TierCapture610F00G09.entries++TierCapture610F00G10.entries++TierCapture610F00G11.entries++TierCapture610F00G12.entries++TierCapture610F00G13.entries++TierCapture610F00G14.entries++TierCapture610F00G15.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : TierCapture610F00G00.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G00.checked
  have h1 : TierCapture610F00G01.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G01.checked
  have h2 : TierCapture610F00G02.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G02.checked
  have h3 : TierCapture610F00G03.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G03.checked
  have h4 : TierCapture610F00G04.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G04.checked
  have h5 : TierCapture610F00G05.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G05.checked
  have h6 : TierCapture610F00G06.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G06.checked
  have h7 : TierCapture610F00G07.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G07.checked
  have h8 : TierCapture610F00G08.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G08.checked
  have h9 : TierCapture610F00G09.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G09.checked
  have h10 : TierCapture610F00G10.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G10.checked
  have h11 : TierCapture610F00G11.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G11.checked
  have h12 : TierCapture610F00G12.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G12.checked
  have h13 : TierCapture610F00G13.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G13.checked
  have h14 : TierCapture610F00G14.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G14.checked
  have h15 : TierCapture610F00G15.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := TierCapture610F00G15.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 1 125 := by
  simp only [entries,List.map_append,TierCapture610F00G00.schedule,TierCapture610F00G01.schedule,TierCapture610F00G02.schedule,TierCapture610F00G03.schedule,TierCapture610F00G04.schedule,TierCapture610F00G05.schedule,TierCapture610F00G06.schedule,TierCapture610F00G07.schedule,TierCapture610F00G08.schedule,TierCapture610F00G09.schedule,TierCapture610F00G10.schedule,TierCapture610F00G11.schedule,TierCapture610F00G12.schedule,TierCapture610F00G13.schedule,TierCapture610F00G14.schedule,TierCapture610F00G15.schedule]
  rfl

end ShielddSecurity.TierCapture610F00

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F00.checked
#print axioms ShielddSecurity.TierCapture610F00.checked

set_option pp.all true in
#check @ShielddSecurity.TierCapture610F00.schedule
#print axioms ShielddSecurity.TierCapture610F00.schedule
