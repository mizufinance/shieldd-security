import ShielddSecurity.SharedSeedBase265
import ShielddSecurity.CapturedBooleanSlots208B0035
import ShielddSecurity.CapturedBooleanSlots208B0038
import ShielddSecurity.CapturedBooleanSlots208B0039
import ShielddSecurity.CapturedBooleanSlots208B0040
import ShielddSecurity.CapturedBooleanSlots208B0041
import ShielddSecurity.CapturedBooleanSlots208B0044
import ShielddSecurity.CapturedBooleanSlots208B0045
import ShielddSecurity.CapturedBooleanSlots208B0052
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedSeedShape265
theorem b24 : (CapturedBooleanSlots208B0035.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b25 : (CapturedBooleanSlots208B0038.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b26 : (CapturedBooleanSlots208B0039.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b27 : (CapturedBooleanSlots208B0040.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b28 : (CapturedBooleanSlots208B0041.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b29 : (CapturedBooleanSlots208B0044.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b30 : (CapturedBooleanSlots208B0045.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b31 : (CapturedBooleanSlots208B0052.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
end ShielddSecurity.SharedSeedShape265

set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b24
#print axioms ShielddSecurity.SharedSeedShape265.b24
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b25
#print axioms ShielddSecurity.SharedSeedShape265.b25
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b26
#print axioms ShielddSecurity.SharedSeedShape265.b26
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b27
#print axioms ShielddSecurity.SharedSeedShape265.b27
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b28
#print axioms ShielddSecurity.SharedSeedShape265.b28
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b29
#print axioms ShielddSecurity.SharedSeedShape265.b29
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b30
#print axioms ShielddSecurity.SharedSeedShape265.b30
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b31
#print axioms ShielddSecurity.SharedSeedShape265.b31
