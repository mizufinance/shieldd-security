import ShielddSecurity.SharedSeedBase265
import ShielddSecurity.CapturedBooleanSlots208B0008
import ShielddSecurity.CapturedBooleanSlots208B0014
import ShielddSecurity.CapturedBooleanSlots208B0015
import ShielddSecurity.CapturedBooleanSlots208B0016
import ShielddSecurity.CapturedBooleanSlots208B0017
import ShielddSecurity.CapturedBooleanSlots208B0018
import ShielddSecurity.CapturedBooleanSlots208B0019
import ShielddSecurity.CapturedBooleanSlots208B0023
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedSeedShape265
theorem b08 : (CapturedBooleanSlots208B0008.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b09 : (CapturedBooleanSlots208B0014.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b10 : (CapturedBooleanSlots208B0015.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b11 : (CapturedBooleanSlots208B0016.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b12 : (CapturedBooleanSlots208B0017.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b13 : (CapturedBooleanSlots208B0018.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b14 : (CapturedBooleanSlots208B0019.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b15 : (CapturedBooleanSlots208B0023.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
end ShielddSecurity.SharedSeedShape265

set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b08
#print axioms ShielddSecurity.SharedSeedShape265.b08
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b09
#print axioms ShielddSecurity.SharedSeedShape265.b09
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b10
#print axioms ShielddSecurity.SharedSeedShape265.b10
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b11
#print axioms ShielddSecurity.SharedSeedShape265.b11
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b12
#print axioms ShielddSecurity.SharedSeedShape265.b12
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b13
#print axioms ShielddSecurity.SharedSeedShape265.b13
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b14
#print axioms ShielddSecurity.SharedSeedShape265.b14
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b15
#print axioms ShielddSecurity.SharedSeedShape265.b15
