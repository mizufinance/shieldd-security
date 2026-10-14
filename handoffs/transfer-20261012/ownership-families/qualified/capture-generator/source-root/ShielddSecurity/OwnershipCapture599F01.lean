-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.OwnershipCapture599F01G00
import ShielddSecurity.OwnershipCapture599F01G01
import ShielddSecurity.OwnershipCapture599F01G02
import ShielddSecurity.OwnershipCapture599F01G03
import ShielddSecurity.OwnershipCapture599F01G04
import ShielddSecurity.OwnershipCapture599F01G05
import ShielddSecurity.OwnershipCapture599F01G06
import ShielddSecurity.OwnershipCapture599F01G07
import ShielddSecurity.OwnershipCapture599F01G08
import ShielddSecurity.OwnershipCapture599F01G09
import ShielddSecurity.OwnershipCapture599F01G10
import ShielddSecurity.OwnershipCapture599F01G11
import ShielddSecurity.OwnershipCapture599F01G12
import ShielddSecurity.OwnershipCapture599F01G13
import ShielddSecurity.OwnershipCapture599F01G14
import ShielddSecurity.OwnershipCapture599F01G15
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipCapture599F01
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
noncomputable def layout : Family := ⟨[(121570,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121572,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],10084,10854,10640⟩
noncomputable def entries : List (Nat × VariableWindowJoin443.Entry) := OwnershipCapture599F01G00.entries++OwnershipCapture599F01G01.entries++OwnershipCapture599F01G02.entries++OwnershipCapture599F01G03.entries++OwnershipCapture599F01G04.entries++OwnershipCapture599F01G05.entries++OwnershipCapture599F01G06.entries++OwnershipCapture599F01G07.entries++OwnershipCapture599F01G08.entries++OwnershipCapture599F01G09.entries++OwnershipCapture599F01G10.entries++OwnershipCapture599F01G11.entries++OwnershipCapture599F01G12.entries++OwnershipCapture599F01G13.entries++OwnershipCapture599F01G14.entries++OwnershipCapture599F01G15.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : OwnershipCapture599F01G00.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G00.checked
  have h1 : OwnershipCapture599F01G01.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G01.checked
  have h2 : OwnershipCapture599F01G02.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G02.checked
  have h3 : OwnershipCapture599F01G03.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G03.checked
  have h4 : OwnershipCapture599F01G04.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G04.checked
  have h5 : OwnershipCapture599F01G05.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G05.checked
  have h6 : OwnershipCapture599F01G06.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G06.checked
  have h7 : OwnershipCapture599F01G07.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G07.checked
  have h8 : OwnershipCapture599F01G08.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G08.checked
  have h9 : OwnershipCapture599F01G09.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G09.checked
  have h10 : OwnershipCapture599F01G10.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G10.checked
  have h11 : OwnershipCapture599F01G11.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G11.checked
  have h12 : OwnershipCapture599F01G12.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G12.checked
  have h13 : OwnershipCapture599F01G13.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G13.checked
  have h14 : OwnershipCapture599F01G14.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G14.checked
  have h15 : OwnershipCapture599F01G15.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := OwnershipCapture599F01G15.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 1 125 := by
  simp only [entries,List.map_append,OwnershipCapture599F01G00.schedule,OwnershipCapture599F01G01.schedule,OwnershipCapture599F01G02.schedule,OwnershipCapture599F01G03.schedule,OwnershipCapture599F01G04.schedule,OwnershipCapture599F01G05.schedule,OwnershipCapture599F01G06.schedule,OwnershipCapture599F01G07.schedule,OwnershipCapture599F01G08.schedule,OwnershipCapture599F01G09.schedule,OwnershipCapture599F01G10.schedule,OwnershipCapture599F01G11.schedule,OwnershipCapture599F01G12.schedule,OwnershipCapture599F01G13.schedule,OwnershipCapture599F01G14.schedule,OwnershipCapture599F01G15.schedule]
  rfl

end ShielddSecurity.OwnershipCapture599F01

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F01.checked
#print axioms ShielddSecurity.OwnershipCapture599F01.checked

set_option pp.all true in
#check @ShielddSecurity.OwnershipCapture599F01.schedule
#print axioms ShielddSecurity.OwnershipCapture599F01.schedule
