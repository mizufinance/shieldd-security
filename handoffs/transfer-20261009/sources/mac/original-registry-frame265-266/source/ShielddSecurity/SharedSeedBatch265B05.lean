import ShielddSecurity.SharedSeedBase265
import ShielddSecurity.CapturedBooleanSlots208B0070
import ShielddSecurity.CapturedBooleanSlots208B0071
import ShielddSecurity.CapturedBooleanSlots208B0072
import ShielddSecurity.CapturedBooleanSlots208B0073
import ShielddSecurity.CapturedBooleanSlots208B0074
import ShielddSecurity.CapturedBooleanSlots208B0075
import ShielddSecurity.CapturedBooleanSlots208B0076
import ShielddSecurity.CapturedBooleanSlots208B0077
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedSeedShape265
theorem b40 : (CapturedBooleanSlots208B0070.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b41 : (CapturedBooleanSlots208B0071.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b42 : (CapturedBooleanSlots208B0072.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b43 : (CapturedBooleanSlots208B0073.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b44 : (CapturedBooleanSlots208B0074.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b45 : (CapturedBooleanSlots208B0075.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b46 : (CapturedBooleanSlots208B0076.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b47 : (CapturedBooleanSlots208B0077.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
end ShielddSecurity.SharedSeedShape265

set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b40
#print axioms ShielddSecurity.SharedSeedShape265.b40
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b41
#print axioms ShielddSecurity.SharedSeedShape265.b41
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b42
#print axioms ShielddSecurity.SharedSeedShape265.b42
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b43
#print axioms ShielddSecurity.SharedSeedShape265.b43
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b44
#print axioms ShielddSecurity.SharedSeedShape265.b44
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b45
#print axioms ShielddSecurity.SharedSeedShape265.b45
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b46
#print axioms ShielddSecurity.SharedSeedShape265.b46
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b47
#print axioms ShielddSecurity.SharedSeedShape265.b47
