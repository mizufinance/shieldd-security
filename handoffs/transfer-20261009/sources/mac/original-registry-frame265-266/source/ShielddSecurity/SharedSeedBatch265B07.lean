import ShielddSecurity.SharedSeedBase265
import ShielddSecurity.CapturedBooleanSlots208B0087
import ShielddSecurity.CapturedBooleanSlots208B0088
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedSeedShape265
theorem b56 : (CapturedBooleanSlots208B0087.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
theorem b57 : (CapturedBooleanSlots208B0088.slots.map Prod.snd).all (fun column => decide (Shape column))=true := by decide +kernel
end ShielddSecurity.SharedSeedShape265

set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b56
#print axioms ShielddSecurity.SharedSeedShape265.b56
set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.b57
#print axioms ShielddSecurity.SharedSeedShape265.b57
