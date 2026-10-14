-- GENERATED from families.json by generate.py. Do not hand edit.
import ShielddSecurity.PayloadCapture558F00G00
import ShielddSecurity.PayloadCapture558F00G01
import ShielddSecurity.PayloadCapture558F00G02
import ShielddSecurity.PayloadCapture558F00G03
import ShielddSecurity.PayloadCapture558F00G04
import ShielddSecurity.PayloadCapture558F00G05
import ShielddSecurity.PayloadCapture558F00G06
import ShielddSecurity.PayloadCapture558F00G07
import ShielddSecurity.PayloadCapture558F00G08
import ShielddSecurity.PayloadCapture558F00G09
import ShielddSecurity.PayloadCapture558F00G10
import ShielddSecurity.PayloadCapture558F00G11
import ShielddSecurity.PayloadCapture558F00G12
import ShielddSecurity.PayloadCapture558F00G13
import ShielddSecurity.PayloadCapture558F00G14
import ShielddSecurity.PayloadCapture558F00G15
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadCapture558F00
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562
def layout : Family := ⟨[(87778,1),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87780,1),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],4931,5436,5295⟩
def entries : List (Nat × VariableWindowJoin443.Entry) := PayloadCapture558F00G00.entries++PayloadCapture558F00G01.entries++PayloadCapture558F00G02.entries++PayloadCapture558F00G03.entries++PayloadCapture558F00G04.entries++PayloadCapture558F00G05.entries++PayloadCapture558F00G06.entries++PayloadCapture558F00G07.entries++PayloadCapture558F00G08.entries++PayloadCapture558F00G09.entries++PayloadCapture558F00G10.entries++PayloadCapture558F00G11.entries++PayloadCapture558F00G12.entries++PayloadCapture558F00G13.entries++PayloadCapture558F00G14.entries++PayloadCapture558F00G15.entries
theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by
  have h0 : PayloadCapture558F00G00.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G00.checked
  have h1 : PayloadCapture558F00G01.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G01.checked
  have h2 : PayloadCapture558F00G02.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G02.checked
  have h3 : PayloadCapture558F00G03.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G03.checked
  have h4 : PayloadCapture558F00G04.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G04.checked
  have h5 : PayloadCapture558F00G05.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G05.checked
  have h6 : PayloadCapture558F00G06.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G06.checked
  have h7 : PayloadCapture558F00G07.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G07.checked
  have h8 : PayloadCapture558F00G08.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G08.checked
  have h9 : PayloadCapture558F00G09.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G09.checked
  have h10 : PayloadCapture558F00G10.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G10.checked
  have h11 : PayloadCapture558F00G11.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G11.checked
  have h12 : PayloadCapture558F00G12.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G12.checked
  have h13 : PayloadCapture558F00G13.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G13.checked
  have h14 : PayloadCapture558F00G14.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G14.checked
  have h15 : PayloadCapture558F00G15.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := PayloadCapture558F00G15.checked
  simp only [entries,List.all_append,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,Bool.true_and]
theorem schedule : entries.map (fun e => e.1)=List.range' 1 125 := by
  simp only [entries,List.map_append,PayloadCapture558F00G00.schedule,PayloadCapture558F00G01.schedule,PayloadCapture558F00G02.schedule,PayloadCapture558F00G03.schedule,PayloadCapture558F00G04.schedule,PayloadCapture558F00G05.schedule,PayloadCapture558F00G06.schedule,PayloadCapture558F00G07.schedule,PayloadCapture558F00G08.schedule,PayloadCapture558F00G09.schedule,PayloadCapture558F00G10.schedule,PayloadCapture558F00G11.schedule,PayloadCapture558F00G12.schedule,PayloadCapture558F00G13.schedule,PayloadCapture558F00G14.schedule,PayloadCapture558F00G15.schedule]
  rfl

end ShielddSecurity.PayloadCapture558F00

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00.checked
#print axioms ShielddSecurity.PayloadCapture558F00.checked

set_option pp.all true in
#check @ShielddSecurity.PayloadCapture558F00.schedule
#print axioms ShielddSecurity.PayloadCapture558F00.schedule
